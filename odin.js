const path = require("path");
const fs = require("fs");
const http = require("http");
const express = require("express");
const cors = require("cors");
const { Server } = require("socket.io");

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(cors());
app.use(express.json());

const PORT = process.env.PORT || 10000;

const CRYPTO_API =
    "https://api.crypto.com/exchange/v1";

const CRYPTO_DCM_API =
    "https://api.crypto.com/dcm/v1";

const CONFIG = {
    underlying: "BTC",
    underlyingIndex: "BTCUSD-INDEX@CdnaFunded",
    fallbackUnderlyingIndex: "BTCUSD-INDEX",
    underlyingPerp: "BTCUSD-PERP",

    collectionSeconds: 180,

    pollIntervalMs: 1000,

    /*
     * DCM has 32,000+ BINARY_OPTION instruments.
     * Keep the instrument cache and refresh it once per minute.
     */
    instrumentRefreshMs: 60000,

    contractSelectionHorizonMs:
        14 *
        24 *
        60 *
        60 *
        1000,

    roundDurationMs:
        15 *
        60 *
        1000,

    forecastStabilityRequired: 3,

    minimumForecastConfidence: 8,

    minimumDataQuality: 85,

    minimumForecastSignals: 1,

    maxIndexAgeMs: 5000,

    /*
     * Official paper W/L accounting begins after the current
     * update/testing day. Everything before this date remains
     * available as round history but is not added to the official
     * daily W/L record.
     */
    officialRecordStartDate: "2026-09-13",

    dailyResetHourET: 23,
    dailyResetMinuteET: 59,

    maxPriceHistory: 900,
    maxTradeHistory: 900,
    maxOrderBookHistory: 300,

    forecastHistoryLimit: 500
};

let state = {
    connected: false,

    serverTime: Date.now(),

    btcPrice: null,
    btcIndexPrice: null,
    btcIndexTimestamp: null,
    btcIndexSource: null,
    btcIndexStale: false,
    btcIndexAgeMs: null,

    strikePrice: null,
    strikeDistance: null,
    strikeDistancePct: null,

    contractSymbol: null,
    contractExpiry: null,
    secondsRemaining: null,

    contractBid: null,
    contractAsk: null,
    contractMid: null,

    marketProbability: null,

    phase: "WAITING",

    forecast: "WAIT",
    forecastProbability: null,
    forecastConfidence: null,
    forecastReason: null,

    modelScore: 0,

    momentum1m: null,
    momentum3m: null,
    momentum5m: null,

    volatility1m: null,
    volatility3m: null,

    velocity: null,
    acceleration: null,

    orderBookImbalance: null,
    tradeFlow: null,

    vwap: null,

    distanceZScore: null,

    dataQuality: 0,

    lastUpdate: null,

    collectionStartedAt: null,

    activeRoundId: null,

    recordDate: null,
    officialRecordEligible: false,
    dailyWins: 0,
    dailyLosses: 0,
    dailyAccuracy: null,
    dailyRecords: {}
};

const priceHistory = [];
const tradeHistory = [];
const orderBookHistory = [];

const completedRounds = [];

const DATA_DIR =
    process.env.ODIN_DATA_DIR
        ? path.resolve(
              process.env.ODIN_DATA_DIR
          )
        : path.join(
              __dirname,
              "data"
          );

const ROUND_HISTORY_FILE =
    path.join(
        DATA_DIR,
        "odin_round_history.json"
    );

const DAILY_RECORD_FILE =
    path.join(
        DATA_DIR,
        "odin_daily_records.json"
    );

let dailyRecords = {};

let instruments = [];
let currentContract = null;

let lastInstrumentRefresh = 0;
let lastPoll = 0;
let instrumentRefreshInProgress = false;
let pollInProgress = false;

let previousVelocity = null;
let previousPrice = null;

let currentRound = null;

let lastNoContractLog = 0;

let rawBinaryInstruments = [];

let dcmMarketSocket = null;
let dcmMarketSocketRetryTimer = null;
let dcmMarketSocketRequestId = 1;
let dcmIndexCache = null;
let dcmSettlementCache = null;
let dcmSubscribedContractSymbol = null;

function getEasternDateKey(timestamp = now()) {
    const parts = new Intl.DateTimeFormat(
        "en-US",
        {
            timeZone: "America/New_York",
            year: "numeric",
            month: "2-digit",
            day: "2-digit"
        }
    ).formatToParts(
        new Date(timestamp)
    );

    const values = {};

    for (const part of parts) {
        values[part.type] =
            part.value;
    }

    return `${values.year}-${values.month}-${values.day}`;
}

function getEasternTimeParts(timestamp = now()) {
    const parts = new Intl.DateTimeFormat(
        "en-US",
        {
            timeZone: "America/New_York",
            hour: "2-digit",
            minute: "2-digit",
            hour12: false
        }
    ).formatToParts(
        new Date(timestamp)
    );

    const values = {};

    for (const part of parts) {
        values[part.type] =
            part.value;
    }

    return {
        hour: Number(
            values.hour
        ),
        minute: Number(
            values.minute
        )
    };
}

function getDailyDisplayDateKey() {
    const time =
        getEasternTimeParts();

    if (
        time.hour ===
            CONFIG.dailyResetHourET &&
        time.minute >=
            CONFIG.dailyResetMinuteET
    ) {
        return getEasternDateKey(
            now() +
                60 *
                1000
        );
    }

    return getEasternDateKey();
}

function isOfficialRecordDate(
    dateKey = getEasternDateKey()
) {
    return (
        dateKey >=
        CONFIG.officialRecordStartDate
    );
}

function ensureDataDirectory() {
    if (!fs.existsSync(DATA_DIR)) {
        fs.mkdirSync(
            DATA_DIR,
            { recursive: true }
        );
    }
}

function rebuildDailyRecordsFromHistory() {
    const reconstructed = {};

    for (const round of completedRounds) {
        if (
            !round ||
            (round.result !== "WIN" &&
                round.result !== "LOSS") ||
            round.officialRecordCounted !== true
        ) {
            continue;
        }

        const dateKey =
            getEasternDateKey(
                round.resolvedAt ||
                    round.expiry ||
                    now()
            );

        if (!isOfficialRecordDate(dateKey)) {
            continue;
        }

        if (!reconstructed[dateKey]) {
            reconstructed[dateKey] = {
                wins: 0,
                losses: 0,
                total: 0,
                closed: 0
            };
        }

        reconstructed[dateKey].total += 1;
        reconstructed[dateKey].closed += 1;

        if (round.result === "WIN") {
            reconstructed[dateKey].wins += 1;
        } else {
            reconstructed[dateKey].losses += 1;
        }
    }

    for (
        const [
            dateKey,
            record
        ] of Object.entries(
            reconstructed
        )
    ) {
        const existing =
            dailyRecords[dateKey] &&
            typeof dailyRecords[dateKey] ===
                "object"
                ? dailyRecords[dateKey]
                : null;

        if (!existing) {
            dailyRecords[dateKey] =
                record;

            continue;
        }

        dailyRecords[dateKey] = {
            wins: Math.max(
                Number(existing.wins) || 0,
                record.wins
            ),

            losses: Math.max(
                Number(existing.losses) || 0,
                record.losses
            ),

            total: Math.max(
                Number(existing.total) || 0,
                record.total
            ),

            closed: Math.max(
                Number(existing.closed) || 0,
                record.closed
            )
        };
    }
}

function persistJsonFile(
    filePath,
    value
) {
    const tempPath =
        `${filePath}.tmp`;

    fs.writeFileSync(
        tempPath,
        JSON.stringify(
            value,
            null,
            2
        ),
        "utf8"
    );

    fs.renameSync(
        tempPath,
        filePath
    );
}

function loadPersistentRecords() {
    ensureDataDirectory();

    try {
        if (
            fs.existsSync(
                ROUND_HISTORY_FILE
            )
        ) {
            const parsed =
                JSON.parse(
                    fs.readFileSync(
                        ROUND_HISTORY_FILE,
                        "utf8"
                    )
                );

            if (
                Array.isArray(parsed)
            ) {
                for (
                    const round of
                        parsed
                ) {
                    if (
                        round &&
                        round.id &&
                        !completedRounds.some(
                            (item) =>
                                item.id ===
                                round.id
                        )
                    ) {
                        completedRounds.push(
                            round
                        );
                    }
                }
            }
        }
    } catch (error) {
        console.error(
            "[ODIN] Round history load error:",
            error.message
        );
    }

    try {
        if (
            fs.existsSync(
                DAILY_RECORD_FILE
            )
        ) {
            const parsed =
                JSON.parse(
                    fs.readFileSync(
                        DAILY_RECORD_FILE,
                        "utf8"
                    )
                );

            if (
                parsed &&
                typeof parsed ===
                    "object"
            ) {
                dailyRecords =
                    parsed;
            }
        }
    } catch (error) {
        console.error(
            "[ODIN] Daily record load error:",
            error.message
        );
    }

    rebuildDailyRecordsFromHistory();

    while (
        completedRounds.length >
        CONFIG.forecastHistoryLimit
    ) {
        completedRounds.shift();
    }
}

function savePersistentRecords() {
    try {
        ensureDataDirectory();

        persistJsonFile(
            ROUND_HISTORY_FILE,
            completedRounds
        );

        persistJsonFile(
            DAILY_RECORD_FILE,
            dailyRecords
        );
    } catch (error) {
        console.error(
            "[ODIN] Record save error:",
            error.message
        );
    }
}

function now() {
    return Date.now();
}

function safeNumber(
    value
) {
    const number =
        Number(value);

    return Number.isFinite(
        number
    )
        ? number
        : null;
}

function clamp(
    value,
    minimum,
    maximum
) {
    return Math.max(
        minimum,
        Math.min(
            maximum,
            value
        )
    );
}

function average(
    values
) {
    const clean =
        values.filter(
            Number.isFinite
        );

    if (!clean.length) {
        return null;
    }

    return (
        clean.reduce(
            (
                sum,
                value
            ) =>
                sum +
                value,
            0
        ) /
        clean.length
    );
}

function standardDeviation(
    values
) {
    const clean =
        values.filter(
            Number.isFinite
        );

    if (clean.length < 2) {
        return null;
    }

    const mean =
        average(
            clean
        );

    const variance =
        clean.reduce(
            (
                sum,
                value
            ) => {
                return (
                    sum +
                    Math.pow(
                        value -
                            mean,
                        2
                    )
                );
            },
            0
        ) /
        clean.length;

    return Math.sqrt(
        variance
    );
}

function weightedAverage(
    items
) {
    if (!items.length) {
        return null;
    }

    let numerator = 0;
    let denominator = 0;

    for (
        const item of items
    ) {
        const value =
            safeNumber(
                item.value
            );

        const weight =
            safeNumber(
                item.weight
            );

        if (
            value === null ||
            weight === null ||
            weight <= 0
        ) {
            continue;
        }

        numerator +=
            value *
            weight;

        denominator +=
            weight;
    }

    if (!denominator) {
        return null;
    }

    return (
        numerator /
        denominator
    );
}

function percentile(
    values,
    percentileValue
) {
    const clean =
        values
            .filter(
                Number.isFinite
            )
            .sort(
                (a, b) =>
                    a - b
            );

    if (!clean.length) {
        return null;
    }

    const index =
        (clean.length - 1) *
        percentileValue;

    const lower =
        Math.floor(
            index
        );

    const upper =
        Math.ceil(
            index
        );

    if (
        lower ===
        upper
    ) {
        return clean[
            lower
        ];
    }

    return (
        clean[lower] +
        (
            clean[upper] -
            clean[lower]
        ) *
        (
            index -
            lower
        )
    );
}

function formatTimestamp(
    timestamp
) {
    if (!timestamp) {
        return null;
    }

    return new Date(
        timestamp
    ).toISOString();
}

function createRoundId(
    expiry
) {
    return `BTC-${expiry}`;
}

async function cryptoRequest(
    endpoint,
    params = {},
    apiRoot = CRYPTO_API
) {
    const url =
        new URL(
            `${apiRoot}/${endpoint}`
        );

    for (
        const [
            key,
            value
        ] of Object.entries(
            params
        )
    ) {
        if (
            value !==
                undefined &&
            value !==
                null &&
            value !==
                ""
        ) {
            url.searchParams.set(
                key,
                String(
                    value
                )
            );
        }
    }

    const response =
        await fetch(
            url.toString(),
            {
                method: "GET",
                headers: {
                    Accept:
                        "application/json"
                }
            }
        );

    if (!response.ok) {
        throw new Error(
            `Crypto.com HTTP ${response.status}`
        );
    }

    const json =
        await response.json();

    if (
        json.code !==
        0
    ) {
        throw new Error(
            json.message ||
                json.original ||
                `Crypto.com API error ${json.code}`
        );
    }

    return json.result;
}

function scheduleDCMMarketSocketReconnect() {
    if (
        dcmMarketSocketRetryTimer
    ) {
        return;
    }

    dcmMarketSocketRetryTimer =
        setTimeout(
            () => {
                dcmMarketSocketRetryTimer =
                    null;

                connectDCMMarketSocket();
            },
            5000
        );
}

function subscribeDCMMarketChannel(
    channel
) {
    if (
        !dcmMarketSocket ||
        dcmMarketSocket.readyState !==
            1
    ) {
        return;
    }

    const request = {
        id:
            String(
                dcmMarketSocketRequestId++
            ),

        method:
            "subscribe",

        params: {
            channels: [
                channel
            ]
        },

        nonce:
            String(
                now()
            )
    };

    dcmMarketSocket.send(
        JSON.stringify(
            request
        )
    );
}

function connectDCMMarketSocket() {
    const WebSocketCtor =
        globalThis.WebSocket;

    if (
        typeof WebSocketCtor !==
        "function"
    ) {
        console.error(
            "[ODIN] Native WebSocket is unavailable; DCM index feed cannot start."
        );

        return;
    }

    if (
        dcmMarketSocket &&
        (
            dcmMarketSocket.readyState ===
                0 ||
            dcmMarketSocket.readyState ===
                1
        )
    ) {
        return;
    }

    try {
        dcmMarketSocket =
            new WebSocketCtor(
                "wss://stream.crypto.com/dcm/v1/market"
            );

        dcmMarketSocket.onopen =
            () => {
                console.log(
                    "[ODIN] DCM market-data websocket connected"
                );

                subscribeDCMMarketChannel(
                    `index.${CONFIG.underlyingIndex}`
                );

                if (
                    dcmSubscribedContractSymbol
                ) {
                    subscribeDCMMarketChannel(
                        `settlement.${dcmSubscribedContractSymbol}`
                    );
                }
            };

        dcmMarketSocket.onmessage =
            (event) => {
                try {
                    const message =
                        JSON.parse(
                            String(
                                event.data
                            )
                        );

                    const result =
                        message?.result ||
                        {};

                    if (
                        Number(message?.code) !== 0 &&
                        message?.method ===
                            "subscribe"
                    ) {
                        console.error(
                            "[ODIN] DCM subscription rejected:",
                            JSON.stringify(
                                message
                            )
                        );
                    }

                    const channel =
                        String(
                            result.channel ||
                                result.subscription ||
                                ""
                        );

                    const data =
                        Array.isArray(
                            result.data
                        )
                            ? result.data
                            : [];

                    const item =
                        data.length
                            ? data[
                                  data.length -
                                      1
                              ]
                            : null;

                    if (
                        channel.startsWith(
                            "index."
                        ) &&
                        item
                    ) {
                        const price =
                            safeNumber(
                                item.v
                            );

                        const timestamp =
                            safeNumber(
                                item.t
                            );

                        if (
                            price !==
                            null
                        ) {
                            dcmIndexCache = {
                                price,

                                timestamp:
                                    timestamp ||
                                    now()
                            };
                        }
                    }

                    if (
                        channel.startsWith(
                            "settlement."
                        ) &&
                        item
                    ) {
                        const price =
                            safeNumber(
                                item.v
                            );

                        const timestamp =
                            safeNumber(
                                item.t
                            );

                        if (
                            price !==
                            null
                        ) {
                            dcmSettlementCache = {
                                price,

                                timestamp:
                                    timestamp ||
                                    now(),

                                symbol:
                                    result.instrument_name ||
                                    dcmSubscribedContractSymbol
                            };
                        }
                    }
                } catch (error) {
                    console.error(
                        "[ODIN] DCM market-data message error:",
                        error.message
                    );
                }
            };

        dcmMarketSocket.onerror =
            (error) => {
                console.error(
                    "[ODIN] DCM market-data websocket error:",
                    error?.message ||
                        error?.error ||
                        "connection failed"
                );
            };

        dcmMarketSocket.onclose =
            () => {
                console.error(
                    "[ODIN] DCM market-data websocket disconnected"
                );

                dcmMarketSocket =
                    null;

                scheduleDCMMarketSocketReconnect();
            };
    } catch (error) {
        console.error(
            "[ODIN] DCM market-data websocket connection error:",
            error.message
        );

        dcmMarketSocket =
            null;

        scheduleDCMMarketSocketReconnect();
    }
}

async function getInstruments() {
    const all = [];

    let cursor = null;

    let page = 0;

    while (true) {
        page += 1;

        const params = {
            inst_type:
                "BINARY_OPTION",

            limit:
                1000
        };

        if (cursor) {
            params.cursor =
                cursor;
        }

        const result =
            await cryptoRequest(
                "public/get-instruments",
                params,
                CRYPTO_DCM_API
            );

        const pageInstruments =
            Array.isArray(
                result?.instruments
            )
                ? result.instruments
                : [];

        all.push(
            ...pageInstruments
        );

        console.log(
            `[ODIN] Instrument page ${page}: ${pageInstruments.length} instruments | Total: ${all.length}`
        );

        const nextCursor =
            result?.next_cursor ||
            result?.nextCursor ||
            null;

        if (
            !nextCursor ||
            pageInstruments.length ===
                0
        ) {
            break;
        }

        cursor =
            nextCursor;
    }

    console.log(
        `[ODIN] Finished instrument pagination at ${all.length} instruments`
    );

    return all;
}

function getInstrumentAttributes(
    instrument
) {
    if (
        instrument?.attributes &&
        typeof instrument.attributes ===
            "object"
    ) {
        return instrument.attributes;
    }

    return {};
}

function getEventMetadata(
    instrument
) {
    if (
        instrument?.event_details &&
        typeof instrument.event_details ===
            "object"
    ) {
        return instrument.event_details;
    }

    if (
        instrument?.eventDetails &&
        typeof instrument.eventDetails ===
            "object"
    ) {
        return instrument.eventDetails;
    }

    return {};
}

function getInstrumentText(
    instrument
) {
    return [
        instrument?.symbol,
        instrument?.display_name,
        instrument?.underlying_symbol,
        instrument?.product_type,
        instrument?.detail_product_type
    ]
        .filter(
            Boolean
        )
        .join(" ")
        .toUpperCase();
}

function isDigitalCurrencyInstrument(
    instrument
) {
    const text =
        getInstrumentText(
            instrument
        );

    const productType =
        String(
            instrument?.product_type ||
                ""
        ).toUpperCase();

    const detailProductType =
        String(
            instrument?.detail_product_type ||
                ""
        ).toUpperCase();

    return (
        productType.includes(
            "DIGITAL"
        ) ||
        productType.includes(
            "CRYPTO"
        ) ||
        detailProductType.includes(
            "DIGITAL"
        ) ||
        detailProductType.includes(
            "CRYPTO"
        ) ||
        text.includes(
            "BITCOIN"
        ) ||
        text.includes(
            "BTC"
        ) ||
        text.includes(
            "ETHEREUM"
        ) ||
        text.includes(
            "ETH"
        )
    );
}

function isBTCStrikeInstrument(
    instrument
) {
    const text =
        getInstrumentText(
            instrument
        );

    const underlying =
        String(
            instrument?.underlying_symbol ||
                ""
        ).toUpperCase();

    return (
        underlying.includes(
            "BTC"
        ) ||
        underlying.includes(
            "XBT"
        ) ||
        text.includes(
            "BITCOIN"
        ) ||
        text.includes(
            "BTC"
        ) ||
        text.includes(
            "XBT"
        )
    );
}

function getStrikeIndex(
    instrument
) {
    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const metadata =
        getEventMetadata(
            instrument
        );

    const candidates = [
        attributes?.STRIKE_INDEX,
        attributes?.strike_index,
        metadata?.STRIKE_INDEX,
        metadata?.strike_index,
        instrument?.strike_index,
        instrument?.strikeIndex
    ];

    for (
        const candidate of
            candidates
    ) {
        const value =
            safeNumber(
                candidate
            );

        if (
            value !==
            null
        ) {
            return value;
        }
    }

    return null;
}

function getStrikeOperator(
    instrument
) {
    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const metadata =
        getEventMetadata(
            instrument
        );

    const candidates = [
        attributes?.STRIKE_OPERATOR,
        attributes?.strike_operator,
        metadata?.STRIKE_OPERATOR,
        metadata?.strike_operator,
        instrument?.strike_operator,
        instrument?.strikeOperator
    ];

    for (
        const candidate of
            candidates
    ) {
        if (
            candidate !==
                undefined &&
            candidate !==
                null
        ) {
            return String(
                candidate
            )
                .trim()
                .toUpperCase();
        }
    }

    return null;
}

function extractStrikePrice(
    instrument
) {
    const directCandidates = [
        instrument?.strike_price,
        instrument?.strikePrice,
        instrument?.strike,
        instrument?.exercise_price,
        instrument?.exercisePrice
    ];

    for (
        const candidate of
            directCandidates
    ) {
        const value =
            safeNumber(
                candidate
            );

        if (
            value !==
            null &&
            value >
                100
        ) {
            return value;
        }
    }

    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const metadata =
        getEventMetadata(
            instrument
        );

    const nestedCandidates = [
        attributes?.STRIKE_PRICE,
        attributes?.strike_price,
        attributes?.STRIKE,
        attributes?.strike,
        metadata?.STRIKE_PRICE,
        metadata?.strike_price,
        metadata?.STRIKE,
        metadata?.strike
    ];

    for (
        const candidate of
            nestedCandidates
    ) {
        const value =
            safeNumber(
                candidate
            );

        if (
            value !==
                null &&
            value >
                100
        ) {
            return value;
        }
    }

    const text =
        [
            instrument?.symbol,
            instrument?.display_name
        ]
            .filter(
                Boolean
            )
            .join(" ");

    const dollarMatches =
        text.match(
            /\$?\s?([0-9]{4,7}(?:\.[0-9]+)?)/g
        );

    if (
        dollarMatches &&
        dollarMatches.length
    ) {
        const values =
            dollarMatches
                .map(
                    (
                        match
                    ) =>
                        safeNumber(
                            match.replace(
                                "$",
                                ""
                            )
                        )
                )
                .filter(
                    (
                        value
                    ) =>
                        value !==
                            null &&
                        value >
                            100
                );

        if (
            values.length
        ) {
            return values[
                values.length -
                    1
            ];
        }
    }

    const symbolParts =
        String(
            instrument?.symbol ||
                ""
        ).split(
            "."
        );

    /*
     * DCM Strike Option symbols can encode the strike using
     * STRIKE_INDEX rather than a literal dollar amount. When
     * the metadata does not contain a direct strike value,
     * the final numeric symbol segment is inspected as a
     * narrow fallback.
     */

    for (
        let index =
            symbolParts.length -
            1;
        index >= 0;
        index--
    ) {
        const numeric =
            safeNumber(
                symbolParts[
                    index
                ]
            );

        if (
            numeric !==
                null &&
            numeric >
                10000
        ) {
            return numeric;
        }
    }

    return null;
}
function normalizeInstrument(
    instrument
) {
    return {
        symbol:
            instrument.symbol ||
            null,

        displayName:
            instrument.display_name ||
            null,

        underlying:
            instrument.underlying_symbol ||
            null,

        productType:
            instrument.product_type ||
            null,

        detailProductType:
            instrument.detail_product_type ||
            null,

        expiry:
            safeNumber(
                instrument.expiry_timestamp_ms
            ),

        tradable:
            Boolean(
                instrument.tradable
            ),

        strikeOperator:
            getStrikeOperator(
                instrument
            ),

        strikeIndex:
            getStrikeIndex(
                instrument
            ),

        strikePrice:
            extractStrikePrice(
                instrument
            ),

        contractSize:
            safeNumber(
                instrument.contract_size
            )
    };
}

function getPeriodCode(
    instrument
) {
    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const metadata =
        getEventMetadata(
            instrument
        );

    const candidates = [
        attributes?.PERIOD_CODE,
        attributes?.period_code,
        metadata?.PERIOD_CODE,
        metadata?.period_code,
        instrument?.PERIOD_CODE,
        instrument?.period_code
    ];

    for (
        const candidate of
            candidates
    ) {
        if (
            candidate !==
                undefined &&
            candidate !==
                null
        ) {
            return String(
                candidate
            )
                .trim()
                .toUpperCase();
        }
    }

    return null;
}

function normalizeTimeValue(
    value
) {
    const numeric =
        safeNumber(
            value
        );

    if (numeric === null) {
        return null;
    }

    if (
        numeric <
        100000000000
    ) {
        return (
            numeric *
            1000
        );
    }

    return numeric;
}

function isFifteenMinuteStrikeInstrument(
    instrument
) {
    if (!instrument) {
        return false;
    }

    const periodCode =
        getPeriodCode(
            instrument
        );

    if (
        periodCode &&
        [
            "15M",
            "M15",
            "15MIN",
            "15MINUTE",
            "15MINUTES",
            "15_MIN",
            "15_MINUTES"
        ].includes(
            periodCode
        )
    ) {
        return true;
    }

    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const metadata =
        getEventMetadata(
            instrument
        );

    const openCandidates = [
        attributes?.OPEN_TIME,
        attributes?.open_time,
        metadata?.OPEN_TIME,
        metadata?.open_time
    ];

    const closeCandidates = [
        attributes?.CLOSE_TIME,
        attributes?.close_time,
        metadata?.CLOSE_TIME,
        metadata?.close_time
    ];

    for (
        const openValue of
            openCandidates
    ) {
        for (
            const closeValue of
                closeCandidates
        ) {
            const openTime =
                normalizeTimeValue(
                    openValue
                );

            const closeTime =
                normalizeTimeValue(
                    closeValue
                );

            if (
                openTime !==
                    null &&
                closeTime !==
                    null
            ) {
                const duration =
                    closeTime -
                    openTime;

                if (
                    Math.abs(
                        duration -
                            CONFIG.roundDurationMs
                    ) <=
                    1000
                ) {
                    return true;
                }
            }
        }
    }

    const text =
        [
            instrument.display_name,
            instrument.symbol
        ]
            .filter(Boolean)
            .join(" ")
            .toUpperCase();

    if (
        /(?:15\s*(?:MIN|MINUTE|MINUTES)|15M)\b/.test(
            text
        )
    ) {
        return true;
    }

    /*
     * Current DCM BTC 15-minute contracts observed by Odin use
     * the intraday `I` symbol segment (for example
     * NX.F.OPT.BTC.I.71.1.20260912). Use that only as a narrow
     * fallback when the contract expires within the next 20 minutes,
     * so an hourly/daily contract is never selected as Odin's round.
     */
    const symbolParts =
        String(
            instrument.symbol ||
                ""
        )
            .toUpperCase()
            .split(".");

    const expiry =
        safeNumber(
            instrument.expiry_timestamp_ms
        );

    if (
        symbolParts[4] ===
            "I" &&
        expiry !== null &&
        expiry > now() &&
        expiry -
            now() <=
            20 *
            60 *
            1000
    ) {
        return true;
    }

    return false;
}

function isAboveStrikeContract(
    instrument
) {
    const operator =
        getStrikeOperator(
            instrument
        );

    if (
        operator === ">" ||
        operator === ">="
    ) {
        return true;
    }

    const displayName =
        String(
            instrument?.display_name ||
                ""
        ).toUpperCase();

    return /(?:BITCOIN|BTC|XBT)\s*>/.test(
        displayName
    );
}

function selectCurrentContract(
    candidates
) {
    const currentTime =
        now();

    const valid =
        candidates
            .filter(
                (
                    instrument
                ) =>
                    instrument &&
                    instrument.tradable !==
                        false &&
                    isFifteenMinuteStrikeInstrument(
                        instrument
                    ) &&
                    isAboveStrikeContract(
                        instrument
                    ) &&
                    safeNumber(
                        instrument.expiry_timestamp_ms
                    ) !== null &&
                    safeNumber(
                        instrument.expiry_timestamp_ms
                    ) >
                        currentTime
            )
            .map(
                (
                    instrument
                ) => ({
                    instrument,

                    expiry:
                        safeNumber(
                            instrument.expiry_timestamp_ms
                        ),

                    strike:
                        extractStrikePrice(
                            instrument
                        ),

                    strikeIndex:
                        getStrikeIndex(
                            instrument
                        ),

                    operator:
                        getStrikeOperator(
                            instrument
                        )
                })
            );

    if (!valid.length) {
        return null;
    }

    const btcPrice =
        state.btcIndexPrice !==
        null
            ? state.btcIndexPrice
            : state.btcPrice;

    const withStrikes =
        valid.filter(
            (item) =>
                item.strike !==
                null
        );

    let selected = null;

    if (
        btcPrice !== null &&
        withStrikes.length
    ) {
        selected =
            withStrikes.sort(
                (
                    a,
                    b
                ) => {
                    const aDistance =
                        Math.abs(
                            a.strike -
                                btcPrice
                        );

                    const bDistance =
                        Math.abs(
                            b.strike -
                                btcPrice
                        );

                    if (
                        aDistance !==
                        bDistance
                    ) {
                        return (
                            aDistance -
                            bDistance
                        );
                    }

                    return (
                        a.expiry -
                        b.expiry
                    );
                }
            )[0];
    }

    if (!selected) {
        selected =
            valid.sort(
                (
                    a,
                    b
                ) =>
                    a.expiry -
                    b.expiry
            )[0];
    }

    return selected;
}

async function refreshInstruments() {
    if (
        instrumentRefreshInProgress
    ) {
        return;
    }

    instrumentRefreshInProgress =
        true;

    try {
        const all =
            await getInstruments();

        rawBinaryInstruments =
            all;

        console.log(
            `[ODIN] DCM BINARY_OPTION instruments received: ${all.length}`
        );

        const digitalCurrencyInstruments =
            all.filter(
                isDigitalCurrencyInstrument
            );

        console.log(
            `[ODIN] Digital-currency Binary Options: ${digitalCurrencyInstruments.length}`
        );

        const btcInstruments =
            digitalCurrencyInstruments.filter(
                isBTCStrikeInstrument
            );

        const btcFifteenMinuteInstruments =
            btcInstruments.filter(
                isFifteenMinuteStrikeInstrument
            );

        console.log(
            `[ODIN] BTC Strike candidates after DCM metadata filter: ${btcInstruments.length}`
        );

        console.log(
            `[ODIN] BTC 15-minute Strike candidates: ${btcFifteenMinuteInstruments.length}`
        );

        const withDollarStrikes =
            btcInstruments.filter(
                (
                    instrument
                ) =>
                    extractStrikePrice(
                        instrument
                    ) !== null
            );

        console.log(
            `[ODIN] BTC instruments with detected dollar strikes: ${withDollarStrikes.length}`
        );

        /*
         * Diagnostic #1:
         *
         * BTC is currently not being identified by the
         * metadata filter. Search the ENTIRE digital-currency
         * instrument set for BTC/XBT/BITCOIN and print only
         * compact fields so Render does not truncate the data.
         */

        if (
            digitalCurrencyInstruments.length >
                0 &&
            btcInstruments.length ===
                0
        ) {
            const btcLikeDigitalCurrency =
                digitalCurrencyInstruments.filter(
                    (
                        instrument
                    ) => {
                        const text =
                            getInstrumentText(
                                instrument
                            );

                        return (
                            text.includes(
                                "BTC"
                            ) ||
                            text.includes(
                                "BITCOIN"
                            ) ||
                            text.includes(
                                "XBT"
                            )
                        );
                    }
                );

            console.log(
                `[ODIN] BTC/XBT/BITCOIN matches inside digital-currency Binary Options: ${btcLikeDigitalCurrency.length}`
            );

            const diagnosticSource =
                btcLikeDigitalCurrency.length >
                0
                    ? btcLikeDigitalCurrency
                    : digitalCurrencyInstruments;

            const sample =
                diagnosticSource
                    .slice(
                        0,
                        10
                    )
                    .map(
                        (
                            instrument
                        ) => ({
                            symbol:
                                instrument.symbol,

                            displayName:
                                instrument.display_name,

                            underlying:
                                instrument.underlying_symbol,

                            productType:
                                instrument.product_type,

                            detailProductType:
                                instrument.detail_product_type,

                            expiry:
                                instrument.expiry_timestamp_ms,

                            attributes:
                                instrument.attributes
                        })
                    );

            console.log(
                "[ODIN] BTC diagnostic sample:",
                JSON.stringify(
                    sample,
                    null,
                    2
                )
            );
        }

        /*
         * Diagnostic #2:
         *
         * If BTC contracts exist but strike extraction is failing,
         * print several raw examples so the exact DCM field layout
         * can be handled without guessing.
         */

        if (
            btcInstruments.length >
                0 &&
            withDollarStrikes.length ===
                0
        ) {
            const strikeDiagnostic =
                btcInstruments
                    .slice(
                        0,
                        10
                    )
                    .map(
                        (
                            instrument
                        ) => ({
                            symbol:
                                instrument.symbol,

                            displayName:
                                instrument.display_name,

                            underlying:
                                instrument.underlying_symbol,

                            attributes:
                                instrument.attributes,

                            eventDetails:
                                instrument.event_details
                        })
                    );

            console.log(
                "[ODIN] BTC strike diagnostic sample:",
                JSON.stringify(
                    strikeDiagnostic,
                    null,
                    2
                )
            );
        }

        /*
         * Diagnostic #3:
         *
         * If BTC contracts exist but the 15-minute filter is
         * returning zero, print the period/open/close metadata
         * needed to determine why.
         */

        if (
            btcInstruments.length >
                0 &&
            btcFifteenMinuteInstruments.length ===
                0
        ) {
            const periodDiagnostic =
                btcInstruments
                    .slice(
                        0,
                        20
                    )
                    .map(
                        (
                            instrument
                        ) => {
                            const attributes =
                                getInstrumentAttributes(
                                    instrument
                                );

                            const metadata =
                                getEventMetadata(
                                    instrument
                                );

                            return {
                                symbol:
                                    instrument.symbol,

                                displayName:
                                    instrument.display_name,

                                periodCode:
                                    getPeriodCode(
                                        instrument
                                    ),

                                openTime:
                                    attributes?.OPEN_TIME ||
                                    attributes?.open_time ||
                                    metadata?.OPEN_TIME ||
                                    metadata?.open_time ||
                                    null,

                                closeTime:
                                    attributes?.CLOSE_TIME ||
                                    attributes?.close_time ||
                                    metadata?.CLOSE_TIME ||
                                    metadata?.close_time ||
                                    null,

                                expiry:
                                    instrument.expiry_timestamp_ms
                            };
                        }
                    );

            console.log(
                "[ODIN] BTC 15-minute diagnostic sample:",
                JSON.stringify(
                    periodDiagnostic,
                    null,
                    2
                )
            );
        }

        instruments =
            btcFifteenMinuteInstruments.map(
                normalizeInstrument
            );

        lastInstrumentRefresh =
            now();

        const selected =
            selectCurrentContract(
                btcFifteenMinuteInstruments
            );

        if (selected) {
            currentContract =
                normalizeInstrument(
                    selected.instrument
                );

            dcmSubscribedContractSymbol =
                currentContract.symbol;

            console.log(
                "[ODIN] Current BTC 15-minute contract:",
                JSON.stringify(
                    currentContract
                )
            );

            if (
                dcmMarketSocket &&
                dcmMarketSocket.readyState ===
                    1
            ) {
                subscribeDCMMarketChannel(
                    `settlement.${currentContract.symbol}`
                );
            }
        } else {
            currentContract =
                null;

            dcmSubscribedContractSymbol =
                null;

            if (
                now() -
                    lastNoContractLog >
                10000
            ) {
                console.log(
                    "[ODIN] No current BTC 15-minute Strike Option contract found."
                );

                lastNoContractLog =
                    now();
            }
        }
    } catch (error) {
        console.error(
            "[ODIN] Instrument refresh error:",
            error.message
        );
    } finally {
        instrumentRefreshInProgress =
            false;
    }
}

async function resolveCurrentContract() {
    if (
        !instruments.length ||
        now() -
            lastInstrumentRefresh >=
            CONFIG.instrumentRefreshMs
    ) {
        await refreshInstruments();
    }

    const selected =
        selectCurrentContract(
            rawBinaryInstruments.filter(
                (
                    instrument
                ) =>
                    isBTCStrikeInstrument(
                        instrument
                    )
            )
        );

    if (selected) {
        currentContract =
            normalizeInstrument(
                selected.instrument
            );

        dcmSubscribedContractSymbol =
            currentContract.symbol;

        if (
            dcmMarketSocket &&
            dcmMarketSocket.readyState ===
                1
        ) {
            subscribeDCMMarketChannel(
                `settlement.${currentContract.symbol}`
            );
        }
    }

    return currentContract;
}
function calculateReturns(
    current,
    previous
) {
    if (
        current === null ||
        previous === null ||
        previous === 0
    ) {
        return null;
    }

    return (
        (
            current -
            previous
        ) /
        previous
    ) *
    100;
}

function getRecentPriceWindow(
    milliseconds
) {
    const cutoff =
        now() -
        milliseconds;

    return priceHistory.filter(
        (
            item
        ) =>
            item.timestamp >=
            cutoff
    );
}

function getRecentTradeWindow(
    milliseconds
) {
    const cutoff =
        now() -
        milliseconds;

    return tradeHistory.filter(
        (
            item
        ) =>
            item.timestamp >=
            cutoff
    );
}

function getRecentOrderBookWindow(
    milliseconds
) {
    const cutoff =
        now() -
        milliseconds;

    return orderBookHistory.filter(
        (
            item
        ) =>
            item.timestamp >=
            cutoff
    );
}

function calculateMomentum(
    milliseconds
) {
    const window =
        getRecentPriceWindow(
            milliseconds
        );

    if (
        window.length <
        2
    ) {
        return null;
    }

    const first =
        window[0].price;

    const last =
        window[
            window.length -
                1
        ].price;

    return calculateReturns(
        last,
        first
    );
}

function calculateVolatility(
    milliseconds
) {
    const window =
        getRecentPriceWindow(
            milliseconds
        );

    if (
        window.length <
        3
    ) {
        return null;
    }

    const returns = [];

    for (
        let i = 1;
        i < window.length;
        i++
    ) {
        const previous =
            window[
                i - 1
            ].price;

        const current =
            window[i].price;

        if (
            previous ===
                null ||
            current ===
                null ||
            previous ===
                0
        ) {
            continue;
        }

        returns.push(
            (
                (
                    current -
                    previous
                ) /
                previous
            ) *
            100
        );
    }

    const deviation =
        standardDeviation(
            returns
        );

    if (
        deviation ===
            null
    ) {
        return null;
    }

    return deviation;
}

function calculateVWAP(
    milliseconds
) {
    const window =
        getRecentTradeWindow(
            milliseconds
        );

    if (!window.length) {
        return null;
    }

    let totalValue = 0;
    let totalVolume = 0;

    for (
        const trade of
            window
    ) {
        const price =
            safeNumber(
                trade.price
            );

        const quantity =
            safeNumber(
                trade.quantity
            );

        if (
            price ===
                null ||
            quantity ===
                null ||
            quantity <=
                0
        ) {
            continue;
        }

        totalValue +=
            price *
            quantity;

        totalVolume +=
            quantity;
    }

    if (
        totalVolume <=
        0
    ) {
        return null;
    }

    return (
        totalValue /
        totalVolume
    );
}

function calculateOrderBookImbalance(
    book
) {
    if (!book) {
        return null;
    }

    const bids =
        Array.isArray(
            book.bids
        )
            ? book.bids
            : [];

    const asks =
        Array.isArray(
            book.asks
        )
            ? book.asks
            : [];

    let bidVolume = 0;
    let askVolume = 0;

    for (
        const level of
            bids
    ) {
        const quantity =
            safeNumber(
                level?.[1]
            );

        if (
            quantity !==
                null
        ) {
            bidVolume +=
                quantity;
        }
    }

    for (
        const level of
            asks
    ) {
        const quantity =
            safeNumber(
                level?.[1]
            );

        if (
            quantity !==
                null
        ) {
            askVolume +=
                quantity;
        }
    }

    const total =
        bidVolume +
        askVolume;

    if (
        total <=
        0
    ) {
        return null;
    }

    return (
        (
            bidVolume -
            askVolume
        ) /
        total
    );
}

function calculateTradeFlow(
    trades
) {
    if (
        !Array.isArray(
            trades
        ) ||
        !trades.length
    ) {
        return null;
    }

    let buyVolume = 0;
    let sellVolume = 0;

    for (
        const trade of
            trades
    ) {
        const quantity =
            safeNumber(
                trade.q ||
                    trade.quantity
            );

        if (
            quantity ===
                null ||
            quantity <=
                0
        ) {
            continue;
        }

        const side =
            String(
                trade.s ||
                    trade.side ||
                    ""
            ).toUpperCase();

        if (
            side ===
            "BUY"
        ) {
            buyVolume +=
                quantity;
        } else if (
            side ===
            "SELL"
        ) {
            sellVolume +=
                quantity;
        }
    }

    const total =
        buyVolume +
        sellVolume;

    if (
        total <=
        0
    ) {
        return null;
    }

    return (
        (
            buyVolume -
            sellVolume
        ) /
        total
    );
}

function calculateDistanceMetrics() {
    if (
        state.btcIndexPrice ===
            null ||
        state.strikePrice ===
            null
    ) {
        state.strikeDistance =
            null;

        state.strikeDistancePct =
            null;

        state.distanceZScore =
            null;

        return;
    }

    state.strikeDistance =
        state.btcIndexPrice -
        state.strikePrice;

    state.strikeDistancePct =
        (
            state.strikeDistance /
            state.strikePrice
        ) *
        100;

    const distances =
        priceHistory
            .map(
                (
                    item
                ) => {
                    if (
                        item.price ===
                            null
                    ) {
                        return null;
                    }

                    return (
                        item.price -
                        state.strikePrice
                    );
                }
            )
            .filter(
                Number.isFinite
            );

    if (
        distances.length <
        3
    ) {
        state.distanceZScore =
            null;

        return;
    }

    const mean =
        average(
            distances
        );

    const deviation =
        standardDeviation(
            distances
        );

    if (
        mean ===
            null ||
        deviation ===
            null ||
        deviation ===
            0
    ) {
        state.distanceZScore =
            null;

        return;
    }

    state.distanceZScore =
        (
            state.strikeDistance -
            mean
        ) /
        deviation;
}

function calculateDataQuality() {
    const qualityParts = [
        state.btcPrice !==
            null
            ? 1
            : 0,

        state.btcIndexPrice !==
            null &&
        !state.btcIndexStale
            ? 1
            : 0,

        state.momentum1m !==
            null
            ? 1
            : 0,

        state.momentum3m !==
            null
            ? 1
            : 0,

        state.volatility1m !==
            null
            ? 1
            : 0,

        state.orderBookImbalance !==
            null
            ? 1
            : 0,

        state.tradeFlow !==
            null
            ? 1
            : 0
    ];

    state.dataQuality =
        (
            qualityParts.reduce(
                (
                    a,
                    b
                ) =>
                    a + b,
                0
            ) /
            qualityParts.length
        ) *
        100;
}

async function collectMarketData() {
    try {
        const [
            index,
            ticker,
            book,
            trades
        ] =
            await Promise.all([
                getBTCIndex(),
                getBTCPerpTicker(),
                getBTCBook(),
                getBTCTrades()
            ]);

        if (ticker) {
            state.btcPrice =
                ticker.last;

            state.lastUpdate =
                ticker.timestamp ||
                now();

            if (
                state.btcPrice !==
                    null
            ) {
                priceHistory.push({
                    timestamp:
                        now(),

                    price:
                        state.btcPrice
                });
            }
        }

        if (index) {
            state.btcIndexPrice =
                index.price;

            state.btcIndexTimestamp =
                index.timestamp ||
                now();

            state.btcIndexSource =
                index.source ||
                null;

            state.btcIndexAgeMs =
                Math.max(
                    0,
                    now() -
                        state.btcIndexTimestamp
                );

            state.btcIndexStale =
                state.btcIndexAgeMs >
                CONFIG.maxIndexAgeMs;
        } else {
            state.btcIndexPrice =
                null;

            state.btcIndexTimestamp =
                null;

            state.btcIndexSource =
                null;

            state.btcIndexAgeMs =
                null;

            state.btcIndexStale =
                true;
        }

        if (book) {
            const imbalance =
                calculateOrderBookImbalance(
                    book
                );

            state.orderBookImbalance =
                imbalance;

            orderBookHistory.push({
                timestamp:
                    now(),

                imbalance
            });
        }

        if (
            Array.isArray(
                trades
            )
        ) {
            for (
                const trade of
                    trades
            ) {
                const timestamp =
                    safeNumber(
                        trade.t ||
                            trade.timestamp
                    ) ||
                    now();

                const price =
                    safeNumber(
                        trade.p ||
                            trade.price
                    );

                const quantity =
                    safeNumber(
                        trade.q ||
                            trade.quantity
                    );

                const side =
                    trade.s ||
                    trade.side ||
                    null;

                if (
                    price !==
                        null &&
                    quantity !==
                        null
                ) {
                    tradeHistory.push({
                        timestamp,
                        price,
                        quantity,
                        side
                    });
                }
            }
        }

        state.tradeFlow =
            calculateTradeFlow(
                trades
            );

        state.momentum1m =
            calculateMomentum(
                60 *
                    1000
            );

        state.momentum3m =
            calculateMomentum(
                3 *
                    60 *
                    1000
            );

        state.momentum5m =
            calculateMomentum(
                5 *
                    60 *
                    1000
            );

        state.volatility1m =
            calculateVolatility(
                60 *
                    1000
            );

        state.volatility3m =
            calculateVolatility(
                3 *
                    60 *
                    1000
            );

        state.vwap =
            calculateVWAP(
                5 *
                    60 *
                    1000
            );

        calculateDistanceMetrics();

        calculateDataQuality();

        while (
            priceHistory.length >
            CONFIG.maxPriceHistory
        ) {
            priceHistory.shift();
        }

        while (
            tradeHistory.length >
            CONFIG.maxTradeHistory
        ) {
            tradeHistory.shift();
        }

        while (
            orderBookHistory.length >
            CONFIG.maxOrderBookHistory
        ) {
            orderBookHistory.shift();
        }
    } catch (error) {
        console.error(
            "[ODIN] Market data collection error:",
            error.message
        );
    }
}

async function getBTCIndex() {
    /*
     * Prefer the authoritative DCM websocket cache.
     *
     * The websocket subscription uses the DCM market-data
     * endpoint and the current configured CdnaFunded index.
     */

    if (
        dcmIndexCache &&
        dcmIndexCache.price !==
            null
    ) {
        const age =
            now() -
            dcmIndexCache.timestamp;

        if (
            age <=
            CONFIG.maxIndexAgeMs
        ) {
            return {
                price:
                    dcmIndexCache.price,

                timestamp:
                    dcmIndexCache.timestamp,

                source:
                    "DCM_INDEX"
            };
        }
    }

    /*
     * Do not silently replace the authoritative DCM index with
     * the perp price. A perp price is useful for market context,
     * but it is not the Strike Option settlement index.
     */

    try {
        const result =
            await cryptoRequest(
                "public/get-valuations",
                {
                    instrument_name:
                        CONFIG.underlyingIndex,

                    valuation_type:
                        "index_price",

                    count:
                        1
                }
            );

        const valuation =
            Array.isArray(
                result?.data
            )
                ? result.data[0]
                : Array.isArray(
                    result?.valuations
                )
                    ? result.valuations[0]
                    : result;

        const price =
            safeNumber(
                valuation?.v ||
                    valuation?.value ||
                    valuation?.index_price
            );

        const timestamp =
            safeNumber(
                valuation?.t ||
                    valuation?.timestamp
            );

        if (
            price !==
                null
        ) {
            return {
                price,

                timestamp:
                    timestamp ||
                    now(),

                source:
                    "EXCHANGE_INDEX"
            };
        }
    } catch (error) {
        /*
         * The Exchange valuation endpoint is only a fallback
         * data source. It must never be mislabeled as DCM_INDEX.
         */
    }

    return null;
}

async function getBTCPerpTicker() {
    try {
        const result =
            await cryptoRequest(
                "public/get-ticker",
                {
                    instrument_name:
                        CONFIG.underlyingPerp
                }
            );

        const ticker =
            Array.isArray(
                result?.data
            )
                ? result.data[0]
                : Array.isArray(
                    result?.tickers
                )
                    ? result.tickers[0]
                    : result;

        if (!ticker) {
            return null;
        }

        return {
            last:
                safeNumber(
                    ticker.a ||
                        ticker.last_price ||
                        ticker.last
                ),

            timestamp:
                safeNumber(
                    ticker.t ||
                        ticker.timestamp
                ) ||
                now()
        };
    } catch (error) {
        return null;
    }
}

async function getBTCBook() {
    try {
        const result =
            await cryptoRequest(
                "public/get-book",
                {
                    instrument_name:
                        CONFIG.underlyingPerp,

                    depth:
                        20
                }
            );

        const book =
            Array.isArray(
                result?.data
            )
                ? result.data[0]
                : result;

        return book || null;
    } catch (error) {
        return null;
    }
}

async function getBTCTrades() {
    try {
        const result =
            await cryptoRequest(
                "public/get-trades",
                {
                    instrument_name:
                        CONFIG.underlyingPerp,

                    count:
                        50
                }
            );

        if (
            Array.isArray(
                result?.data
            )
        ) {
            return result.data;
        }

        if (
            Array.isArray(
                result?.trades
            )
        ) {
            return result.trades;
        }

        if (
            Array.isArray(
                result
            )
        ) {
            return result;
        }

        return [];
    } catch (error) {
        return [];
    }
}

async function collectContractData() {
    if (
        !currentContract ||
        !currentContract.instrument
    ) {
        state.contractBid =
            null;

        state.contractAsk =
            null;

        state.contractMid =
            null;

        state.marketProbability =
            null;

        return;
    }

    const symbol =
        currentContract.instrument
            .symbol;

    if (!symbol) {
        return;
    }

    try {
        const result =
            await cryptoRequest(
                "public/get-ticker",
                {
                    instrument_name:
                        symbol
                },
                CRYPTO_DCM_API
            );

        const ticker =
            Array.isArray(
                result?.data
            )
                ? result.data[0]
                : Array.isArray(
                    result?.tickers
                )
                    ? result.tickers[0]
                    : result;

        if (!ticker) {
            return;
        }

        const bid =
            safeNumber(
                ticker.b ||
                    ticker.bid_price ||
                    ticker.bid
            );

        const ask =
            safeNumber(
                ticker.k ||
                    ticker.ask_price ||
                    ticker.ask
            );

        const mid =
            bid !== null &&
            ask !== null
                ? (
                    bid +
                    ask
                ) /
                2
                : null;

        state.contractBid =
            bid;

        state.contractAsk =
            ask;

        state.contractMid =
            mid;

        if (
            mid !==
                null
        ) {
            state.marketProbability =
                clamp(
                    mid *
                        10,
                    0,
                    100
                );
        } else {
            state.marketProbability =
                null;
        }
    } catch (error) {
        state.contractBid =
            null;

        state.contractAsk =
            null;

        state.contractMid =
            null;

        state.marketProbability =
            null;
    }
}

function calculateStateMetrics() {
    state.velocity =
        null;

    state.acceleration =
        null;

    if (
        state.btcPrice !==
            null &&
        previousPrice !==
            null
    ) {
        state.velocity =
            state.btcPrice -
            previousPrice;
    }

    if (
        state.velocity !==
            null &&
        previousVelocity !==
            null
    ) {
        state.acceleration =
            state.velocity -
            previousVelocity;
    }

    if (
        state.velocity !==
            null
    ) {
        previousVelocity =
            state.velocity;
    }

    if (
        state.btcPrice !==
            null
    ) {
        previousPrice =
            state.btcPrice;
    }

    calculateDistanceMetrics();

    calculateDataQuality();
}

function calculateForecast() {
    if (
        !currentContract ||
        !currentContract.instrument
    ) {
        state.phase =
            "WAITING";

        state.forecast =
            "WAIT";

        state.forecastProbability =
            null;

        state.forecastConfidence =
            null;

        state.forecastReason =
            "Waiting for a verified BTC 15-minute Strike Option contract.";

        return;
    }

    const expiry =
        safeNumber(
            currentContract.expiry
        );

    const strike =
        safeNumber(
            currentContract.strike
        );

    if (
        expiry ===
            null ||
        strike ===
            null
    ) {
        state.phase =
            "WAITING";

        state.forecast =
            "WAIT";

        state.forecastProbability =
            null;

        state.forecastConfidence =
            null;

        state.forecastReason =
            "Waiting for a verified contract expiry and strike.";

        return;
    }

    state.secondsRemaining =
        Math.max(
            0,
            Math.floor(
                (
                    expiry -
                    now()
                ) /
                1000
            )
        );

    /*
     * A new paper round is created once per contract.
     * Odin does not place a live order.
     */

    const roundId =
        createRoundId(
            expiry
        );

    if (
        !currentRound ||
        currentRound.id !==
            roundId
    ) {
        currentRound = {
            id:
                roundId,

            symbol:
                currentContract
                    .instrument
                    .symbol,

            expiry,

            strike,

            forecast:
                null,

            forecastProbability:
                null,

            confidence:
                null,

            forecastReason:
                null,

            forecastMade:
                false,

            result:
                null,

            finalPrice:
                null,

            resolvedAt:
                null,

            officialRecordCounted:
                false
        };

        state.collectionStartedAt =
            now();

        console.log(
            `[ODIN] Started paper round ${roundId}`
        );
    }

    /*
     * Odin must have the authoritative current DCM index and
     * verified strike before making a forecast.
     */

    if (
        state.btcIndexPrice ===
            null ||
        state.btcIndexStale ||
        state.btcIndexSource !==
            "DCM_INDEX" ||
        state.strikePrice ===
            null
    ) {
        state.phase =
            "SIT_OUT";

        state.forecast =
            "SIT OUT";

        state.forecastProbability =
            50;

        state.forecastConfidence =
            0;

        state.forecastReason =
            "SIT OUT: Odin does not have the authoritative current BTC index and verified strike needed to evaluate this round.";

        currentRound.forecast =
            "SIT OUT";

        currentRound.forecastProbability =
            50;

        currentRound.confidence =
            0;

        currentRound.forecastReason =
            state.forecastReason;

        currentRound.forecastMade =
            true;

        return;
    }

    const elapsed =
        secondsSinceRoundStart();

    if (
        elapsed <
        CONFIG.collectionSeconds
    ) {
        state.phase =
            "COLLECTING";

        state.forecast =
            "WAIT";

        state.forecastProbability =
            null;

        state.forecastConfidence =
            null;

        state.forecastReason =
            `Collecting market data. ${Math.max(
                0,
                CONFIG.collectionSeconds -
                    elapsed
            )} seconds remaining in the collection phase.`;

        return;
    }

    /*
     * The following section creates a transparent paper forecast
     * from the already-collected market measurements.
     *
     * It does not place, route, or recommend a live trade.
     */

    const signals = [];

    if (
        state.momentum1m !==
            null
    ) {
        signals.push({
            name:
                "1m momentum",

            value:
                state.momentum1m,

            weight:
                1
        });
    }

    if (
        state.momentum3m !==
            null
    ) {
        signals.push({
            name:
                "3m momentum",

            value:
                state.momentum3m,

            weight:
                1
        });
    }

    if (
        state.momentum5m !==
            null
    ) {
        signals.push({
            name:
                "5m momentum",

            value:
                state.momentum5m,

            weight:
                0.75
        });
    }

    if (
        state.velocity !==
            null
    ) {
        signals.push({
            name:
                "velocity",

            value:
                state.velocity /
                Math.max(
                    1,
                    state.btcIndexPrice
                ) *
                100,

            weight:
                0.5
        });
    }

    if (
        state.acceleration !==
            null
    ) {
        signals.push({
            name:
                "acceleration",

            value:
                state.acceleration /
                Math.max(
                    1,
                    state.btcIndexPrice
                ) *
                100,

            weight:
                0.25
        });
    }

    if (
        state.orderBookImbalance !==
            null
    ) {
        signals.push({
            name:
                "order book",

            value:
                state.orderBookImbalance *
                0.1,

            weight:
                0.5
        });
    }

    if (
        state.tradeFlow !==
            null
    ) {
        signals.push({
            name:
                "trade flow",

            value:
                state.tradeFlow *
                0.1,

            weight:
                0.5
        });
    }

    if (
        state.strikeDistancePct !==
            null
    ) {
        signals.push({
            name:
                "strike distance",

            value:
                state.strikeDistancePct,

            weight:
                1
        });
    }

    if (
        signals.length <
        CONFIG.minimumForecastSignals
    ) {
        state.phase =
            "WAITING";

        state.forecast =
            "WAIT";

        state.forecastProbability =
            null;

        state.forecastConfidence =
            0;

        state.forecastReason =
            "Waiting for enough market observations to evaluate the paper round.";

        return;
    }

    const weightedSignal =
        weightedAverage(
            signals.map(
                (
                    signal
                ) => ({
                    value:
                        signal.value,

                    weight:
                        signal.weight
                })
            )
        );

    if (
        weightedSignal ===
            null
    ) {
        state.phase =
            "WAITING";

        state.forecast =
            "WAIT";

        state.forecastProbability =
            null;

        state.forecastConfidence =
            0;

        state.forecastReason =
            "Waiting for valid market signals.";

        return;
    }

    /*
     * Keep the probability bounded and transparent.
     * This is a paper-model estimate, not a guarantee of outcome.
     */

    const probability =
        clamp(
            50 +
                weightedSignal *
                    5,
            1,
            99
        );

    const confidence =
        clamp(
            Math.abs(
                probability -
                    50
            ) *
                2,
            0,
            100
        );

    const forecast =
        probability >=
        50
            ? "YES"
            : "NO";

    const strongestSignal =
        signals
            .slice()
            .sort(
                (
                    a,
                    b
                ) =>
                    Math.abs(
                        b.value *
                            b.weight
                    ) -
                    Math.abs(
                        a.value *
                            a.weight
                    )
            )[0];

    state.phase =
        "FORECASTING";

    state.forecast =
        forecast;

    state.forecastProbability =
        probability;

    state.forecastConfidence =
        confidence;

    state.modelScore =
        weightedSignal;

    state.forecastReason =
        strongestSignal
            ? `Paper forecast based on ${strongestSignal.name}, with ${signals.length} available market signals.`
            : "Paper forecast based on available market signals.";

    currentRound.forecast =
        forecast;

    currentRound.forecastProbability =
        probability;

    currentRound.confidence =
        confidence;

    currentRound.forecastReason =
        state.forecastReason;

    currentRound.forecastMade =
        true;
}

function secondsSinceRoundStart() {
    if (
        !currentRound ||
        !currentRound.id
    ) {
        return 0;
    }

    if (
        !state.collectionStartedAt
    ) {
        state.collectionStartedAt =
            now();
    }

    return Math.max(
        0,
        Math.floor(
            (
                now() -
                state.collectionStartedAt
            ) /
            1000
        )
    );
}

function resetDailyDisplayIfNeeded() {
    const displayDate =
        getDailyDisplayDateKey();

    if (
        state.recordDate !==
        displayDate
    ) {
        state.recordDate =
            displayDate;

        state.officialRecordEligible =
            isOfficialRecordDate(
                displayDate
            );

        const record =
            dailyRecords[
                displayDate
            ];

        if (
            record &&
            typeof record ===
                "object"
        ) {
            state.dailyWins =
                Number(
                    record.wins
                ) ||
                0;

            state.dailyLosses =
                Number(
                    record.losses
                ) ||
                0;

            const total =
                state.dailyWins +
                state.dailyLosses;

            state.dailyAccuracy =
                total >
                0
                    ? (
                        state.dailyWins /
                        total
                    ) *
                    100
                    : null;
        } else {
            state.dailyWins =
                0;

            state.dailyLosses =
                0;

            state.dailyAccuracy =
                null;
        }
    }
}

function updateDailyState() {
    resetDailyDisplayIfNeeded();

    const dateKey =
        state.recordDate;

    if (
        !dateKey ||
        !isOfficialRecordDate(
            dateKey
        )
    ) {
        state.officialRecordEligible =
            false;

        state.dailyWins =
            0;

        state.dailyLosses =
            0;

        state.dailyAccuracy =
            null;

        return;
    }

    const record =
        dailyRecords[
            dateKey
        ];

    if (
        !record ||
        typeof record !==
            "object"
    ) {
        state.dailyWins =
            0;

        state.dailyLosses =
            0;

        state.dailyAccuracy =
            null;

        return;
    }

    state.dailyWins =
        Number(
            record.wins
        ) ||
        0;

    state.dailyLosses =
        Number(
            record.losses
        ) ||
        0;

    const total =
        state.dailyWins +
        state.dailyLosses;

    state.dailyAccuracy =
        total >
        0
            ? (
                state.dailyWins /
                total
            ) *
            100
            : null;
}

function countOfficialRoundResult(
    round
) {
    if (
        !round ||
        (
            round.result !==
                "WIN" &&
            round.result !==
                "LOSS"
        )
    ) {
        return;
    }

    if (
        round.officialRecordCounted ===
        true
    ) {
        return;
    }

    const resolvedAt =
        safeNumber(
            round.resolvedAt
        ) ||
        now();

    const dateKey =
        getEasternDateKey(
            resolvedAt
        );

    if (
        !isOfficialRecordDate(
            dateKey
        )
    ) {
        round.officialRecordCounted =
            false;

        return;
    }

    if (
        !dailyRecords[
            dateKey
        ] ||
        typeof dailyRecords[
            dateKey
        ] !==
            "object"
    ) {
        dailyRecords[
            dateKey
        ] = {
            wins:
                0,

            losses:
                0,

            total:
                0,

            closed:
                0
        };
    }

    const record =
        dailyRecords[
            dateKey
        ];

    if (
        round.result ===
        "WIN"
    ) {
        record.wins =
            (
                Number(
                    record.wins
                ) ||
                0
            ) +
            1;
    }

    if (
        round.result ===
        "LOSS"
    ) {
        record.losses =
            (
                Number(
                    record.losses
                ) ||
                0
            ) +
            1;
    }

    record.total =
        (
            Number(
                record.wins
            ) ||
            0
        ) +
        (
            Number(
                record.losses
            ) ||
            0
        );

    record.closed =
        (
            Number(
                record.closed
            ) ||
            0
        ) +
        1;

    round.officialRecordCounted =
        true;

    savePersistentRecords();

    updateDailyState();
}

function getDailyRecord() {
    const dateKey =
        getDailyDisplayDateKey();

    const record =
        dailyRecords[
            dateKey
        ];

    if (
        !record ||
        typeof record !==
            "object"
    ) {
        return {
            wins:
                0,

            losses:
                0,

            total:
                0,

            accuracy:
                null,

            date:
                dateKey,

            eligible:
                isOfficialRecordDate(
                    dateKey
                )
        };
    }

    const wins =
        Number(
            record.wins
        ) ||
        0;

    const losses =
        Number(
            record.losses
        ) ||
        0;

    const total =
        wins +
        losses;

    return {
        wins,

        losses,

        total,

        accuracy:
            total > 0
                ? (
                    wins /
                    total
                ) *
                100
                : null,

        date:
            dateKey,

        eligible:
            isOfficialRecordDate(
                dateKey
            )
    };
}

function pushCompletedRound(
    round
) {
    if (!round) {
        return;
    }

    if (
        completedRounds.some(
            (
                existing
            ) =>
                existing.id ===
                round.id
        )
    ) {
        return;
    }

    completedRounds.push(
        round
    );

    while (
        completedRounds.length >
        CONFIG.forecastHistoryLimit
    ) {
        completedRounds.shift();
    }

    savePersistentRecords();
}

function determineRoundResult(
    round,
    settlementPrice
) {
    if (
        !round ||
        settlementPrice ===
            null ||
        round.strike ===
            null
    ) {
        return null;
    }

    if (
        round.forecast !==
            "YES" &&
        round.forecast !==
            "NO"
    ) {
        return null;
    }

    const yesResult =
        settlementPrice >
        round.strike;

    if (
        round.forecast ===
        "YES"
    ) {
        return yesResult
            ? "WIN"
            : "LOSS";
    }

    return !yesResult
        ? "WIN"
        : "LOSS";
}

function resolveCompletedRound(
    settlementPrice,
    settlementTimestamp
) {
    if (
        !currentRound ||
        currentRound.result ||
        !currentRound.forecastMade
    ) {
        return;
    }

    const expiry =
        safeNumber(
            currentRound.expiry
        );

    if (
        expiry ===
            null
    ) {
        return;
    }

    if (
        now() <
        expiry
    ) {
        return;
    }

    const result =
        determineRoundResult(
            currentRound,
            settlementPrice
        );

    if (
        !result
    ) {
        return;
    }

    currentRound.result =
        result;

    currentRound.settlementPrice =
        settlementPrice;

    currentRound.settlementTimestamp =
        settlementTimestamp ||
        now();

    currentRound.resolvedAt =
        now();

    recordOfficialResult(
        currentRound
    );

    pushCompletedRound(
        currentRound
    );

    console.log(
        `[ODIN] Round ${currentRound.id} resolved: ${result}`
    );
}

function processSettlementCache() {
    if (
        !dcmSettlementCache
    ) {
        return;
    }

    const price =
        safeNumber(
            dcmSettlementCache.price
        );

    const timestamp =
        safeNumber(
            dcmSettlementCache.timestamp
        );

    if (
        price ===
            null
    ) {
        return;
    }

    if (
        !currentRound
    ) {
        return;
    }

    if (
        dcmSettlementCache.symbol &&
        currentRound.symbol &&
        dcmSettlementCache.symbol !==
            currentRound.symbol
    ) {
        return;
    }

    resolveCompletedRound(
        price,
        timestamp
    );
}

function resolveExpiredRoundFromIndex() {
    if (
        !currentRound ||
        currentRound.result ||
        !currentRound.forecastMade
    ) {
        return;
    }

    const expiry =
        safeNumber(
            currentRound.expiry
        );

    if (
        expiry ===
            null ||
        now() <
            expiry
    ) {
        return;
    }

    /*
     * Never use a stale or unrelated price as an official
     * settlement value. The settlement websocket is preferred.
     */

    if (
        dcmSettlementCache &&
        safeNumber(
            dcmSettlementCache.price
        ) !==
            null &&
        (
            !dcmSettlementCache.symbol ||
            !currentRound.symbol ||
            dcmSettlementCache.symbol ===
                currentRound.symbol
        )
    ) {
        resolveCompletedRound(
            safeNumber(
                dcmSettlementCache.price
            ),
            safeNumber(
                dcmSettlementCache.timestamp
            )
        );
    }
}

function updateRoundLifecycle() {
    processSettlementCache();

    resolveExpiredRoundFromIndex();

    if (
        currentRound &&
        currentRound.result
    ) {
        currentRound =
            null;

        state.activeRoundId =
            null;

        state.forecast =
            "WAIT";

        state.forecastProbability =
            null;

        state.forecastConfidence =
            null;

        state.forecastReason =
            "Previous paper round resolved. Waiting for the next BTC 15-minute round.";

        state.phase =
            "WAITING";
    }
}

function updateStateLoop() {
    updateContractState();

    updateRoundLifecycle();

    calculateForecast();

    updateDailyState();

    state.connected =
        true;

    state.serverTime =
        now();

    io.emit(
        "state",
        buildPublicState()
    );
}

async function pollLoop() {
    if (
        pollInProgress
    ) {
        return;
    }

    pollInProgress =
        true;

    try {
        if (
            now() -
                lastInstrumentRefresh >=
            CONFIG.instrumentRefreshMs
        ) {
            await refreshInstruments();

            lastInstrumentRefresh =
                now();
        }

        resolveCurrentContract();

        await collectMarketData();

        updateStateLoop();

        lastPoll =
            now();
    } catch (error) {
        console.error(
            "[ODIN] Poll loop error:",
            error.message
        );
    } finally {
        pollInProgress =
            false;
    }
}

function sendInitialState(
    socket
) {
    socket.emit(
        "state",
        buildPublicState()
    );
}

app.get(
    "/",
    (
        req,
        res
    ) => {
        res.sendFile(
            path.join(
                __dirname,
                "public",
                "index.html"
            )
        );
    }
);

app.get(
    "/api/state",
    (
        req,
        res
    ) => {
        res.json(
            buildPublicState()
        );
    }
);

app.get(
    "/api/history",
    (
        req,
        res
    ) => {
        res.json({
            rounds:
                completedRounds,

            dailyRecords:
                dailyRecords
        });
    }
);

io.on(
    "connection",
    (
        socket
    ) => {
        console.log(
            "[ODIN] Dashboard connected"
        );

        sendInitialState(
            socket
        );

        socket.on(
            "disconnect",
            () => {
                console.log(
                    "[ODIN] Dashboard disconnected"
                );
            }
        );
    }
);

loadPersistentRecords();

updateDailyState();

connectDCMMarketSocket();

setInterval(
    pollLoop,
    CONFIG.pollIntervalMs
);

setInterval(
    resetDailyDisplayIfNeeded,
    1000
);

pollLoop();

server.listen(
    PORT,
    () => {
        console.log(
            `[ODIN] Server listening on port ${PORT}`
        );
    }
);