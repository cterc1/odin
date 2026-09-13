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

    minimumForecastSignals: 3,

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

    for (const [dateKey, record] of Object.entries(reconstructed)) {
        const existing =
            dailyRecords[dateKey] &&
            typeof dailyRecords[dateKey] === "object"
                ? dailyRecords[dateKey]
                : null;

        if (!existing) {
            dailyRecords[dateKey] = record;
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
                for (const round of parsed) {
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
                dailyRecords = parsed;
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
            "[ODIN] Persistent record save error:",
            error.message
        );
    }
}

function getDailyRecord(
    dateKey = getEasternDateKey()
) {
    const record =
        dailyRecords[dateKey];

    if (
        record &&
        typeof record ===
            "object"
    ) {
        return {
            wins: Number(
                record.wins
            ) || 0,
            losses: Number(
                record.losses
            ) || 0,
            total: Number(
                record.total
            ) || 0,
            closed: Number(
                record.closed
            ) || 0
        };
    }

    return {
        wins: 0,
        losses: 0,
        total: 0,
        closed: 0
    };
}

function updateDailyState() {
    const dateKey =
        getDailyDisplayDateKey();

    const eligible =
        isOfficialRecordDate(
            dateKey
        );

    const record =
        eligible
            ? getDailyRecord(
                  dateKey
              )
            : {
                  wins: 0,
                  losses: 0,
                  total: 0,
                  closed: 0
              };

    state.recordDate =
        dateKey;

    state.officialRecordEligible =
        eligible;

    state.dailyWins =
        record.wins;

    state.dailyLosses =
        record.losses;

    state.dailyAccuracy =
        record.total > 0
            ? (
                  record.wins /
                  record.total
              ) *
              100
            : null;

    state.dailyRecords =
        dailyRecords;
}

function recordOfficialResult(
    round
) {
    if (
        !round ||
        (round.result !==
            "WIN" &&
            round.result !==
                "LOSS")
    ) {
        return false;
    }

    const dateKey =
        getEasternDateKey(
            round.resolvedAt ||
                now()
        );

    if (
        !isOfficialRecordDate(
            dateKey
        )
    ) {
        round.officialRecordCounted =
            false;

        return false;
    }

    const record =
        getDailyRecord(
            dateKey
        );

    if (
        round.officialRecordCounted ===
            true
    ) {
        return false;
    }

    record.total += 1;
    record.closed += 1;

    if (
        round.result ===
        "WIN"
    ) {
        record.wins += 1;
    } else {
        record.losses += 1;
    }

    dailyRecords[dateKey] =
        record;

    round.officialRecordCounted =
        true;

    savePersistentRecords();

    return true;
}

function resetDailyDisplayIfNeeded() {
    const time =
        getEasternTimeParts();

    /*
     * The live daily panel is date-keyed, so it naturally starts
     * at 0-0 on the new ET date. This check also makes the 11:59 PM
     * reset explicit in the server state without deleting history.
     */
    if (
        time.hour ===
            CONFIG.dailyResetHourET &&
        time.minute ===
            CONFIG.dailyResetMinuteET
    ) {
        updateDailyState();
    }
}

function now() {
    return Date.now();
}

function safeNumber(value) {
    const number = Number(value);

    if (!Number.isFinite(number)) {
        return null;
    }

    return number;
}

function clamp(value, min, max) {
    return Math.max(
        min,
        Math.min(max, value)
    );
}

function average(values) {
    const clean = values.filter(
        Number.isFinite
    );

    if (!clean.length) {
        return null;
    }

    return clean.reduce(
        (a, b) => a + b,
        0
    ) / clean.length;
}

function standardDeviation(values) {
    const clean = values.filter(
        Number.isFinite
    );

    if (clean.length < 2) {
        return null;
    }

    const mean = average(clean);

    const variance =
        clean.reduce(
            (sum, value) => {
                return (
                    sum +
                    Math.pow(
                        value - mean,
                        2
                    )
                );
            },
            0
        ) / clean.length;

    return Math.sqrt(variance);
}

function weightedAverage(items) {
    if (!items.length) {
        return null;
    }

    let numerator = 0;
    let denominator = 0;

    for (const item of items) {
        const value = safeNumber(
            item.value
        );

        const weight = safeNumber(
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
    const clean = values
        .filter(Number.isFinite)
        .sort(
            (a, b) => a - b
        );

    if (!clean.length) {
        return null;
    }

    const index =
        (clean.length - 1) *
        percentileValue;

    const lower =
        Math.floor(index);

    const upper =
        Math.ceil(index);

    if (lower === upper) {
        return clean[lower];
    }

    return (
        clean[lower] +
        (
            clean[upper] -
            clean[lower]
        ) *
        (index - lower)
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
    const url = new URL(
        `${apiRoot}/${endpoint}`
    );

    for (
        const [
            key,
            value
        ] of Object.entries(params)
    ) {
        if (
            value !==
                undefined &&
            value !== null &&
            value !== ""
        ) {
            url.searchParams.set(
                key,
                String(value)
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

    if (json.code !== 0) {
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
            dcmMarketSocketRequestId++,

        method:
            "subscribe",

        params: {
            channels: [
                channel
            ]
        },

        nonce: now()
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
            () => {
                console.error(
                    "[ODIN] DCM market-data websocket error"
                );
            };

        dcmMarketSocket.onclose =
            () => {
                console.log(
                    "[ODIN] DCM market-data websocket disconnected"
                );

                dcmMarketSocket =
                    null;

                scheduleDCMMarketSocketReconnect();
            };
    } catch (error) {
        dcmMarketSocket =
            null;

        console.error(
            "[ODIN] DCM market-data websocket connection error:",
            error.message
        );

        scheduleDCMMarketSocketReconnect();
    }
}

async function getBTCIndex() {
    /*
     * Strike Options use the CDNA-funded BTC index.
     * The DCM market-data websocket exposes the index channel
     * for the exact underlying used by the Strike instrument.
     *
     * Prefer that live feed. The REST Exchange index remains only
     * a fallback so Odin can continue displaying diagnostics if the
     * DCM websocket is temporarily unavailable.
     */

    if (
        dcmIndexCache &&
        safeNumber(
            dcmIndexCache.price
        ) !== null &&
        safeNumber(
            dcmIndexCache.timestamp
        ) !== null &&
        now() -
            dcmIndexCache.timestamp <=
            5000
    ) {
        return {
            price: safeNumber(
                dcmIndexCache.price
            ),

            timestamp:
                safeNumber(
                    dcmIndexCache.timestamp
                ),

            source:
                "DCM_INDEX"
        };
    }

    try {
        const result =
            await cryptoRequest(
                "public/get-valuations",
                {
                    instrument_name:
                        CONFIG.fallbackUnderlyingIndex,

                    valuation_type:
                        "index_price",

                    count: 1
                }
            );

        const item =
            result?.data?.[0];

        if (!item) {
            return null;
        }

        return {
            price: safeNumber(
                item.v
            ),

            timestamp:
                safeNumber(
                    item.t
                ),

            source:
                "EXCHANGE_INDEX_FALLBACK"
        };
    } catch (error) {
        return null;
    }
}

async function getBTCPerpTicker() {
    const result =
        await cryptoRequest(
            "public/get-tickers",
            {
                instrument_name:
                    CONFIG.underlyingPerp
            }
        );

    const ticker =
        result?.data?.[0];

    if (!ticker) {
        return null;
    }

    return {
        last: safeNumber(
            ticker.a
        ),

        bid: safeNumber(
            ticker.b
        ),

        ask: safeNumber(
            ticker.k
        ),

        bidSize: safeNumber(
            ticker.bs
        ),

        askSize: safeNumber(
            ticker.ks
        ),

        volume: safeNumber(
            ticker.v
        ),

        timestamp: safeNumber(
            ticker.t
        )
    };
}

async function getBTCBook() {
    const result =
        await cryptoRequest(
            "public/get-book",
            {
                instrument_name:
                    CONFIG.underlyingPerp,

                depth: 25
            }
        );

    return (
        result?.data?.[0] ||
        null
    );
}

async function getBTCTrades() {
    const result =
        await cryptoRequest(
            "public/get-trades",
            {
                instrument_name:
                    CONFIG.underlyingPerp,

                count: 50
            }
        );

    return result?.data || [];
}

async function getInstruments() {
    let allInstruments = [];
    let cursor = null;

    for (
        let page = 0;
        page < 1000;
        page++
    ) {
        const params = {
            inst_type:
                "BINARY_OPTION",

            limit: 1000,

            since: 0
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

        const pageData =
            Array.isArray(
                result?.data
            )
                ? result.data
                : [];

        allInstruments =
            allInstruments.concat(
                pageData
            );

        console.log(
            `[ODIN] Instrument page ${page + 1}: ${pageData.length} instruments | Total: ${allInstruments.length}`
        );

        const nextCursor =
            result?.next_cursor;

        if (
            !nextCursor ||
            !pageData.length
        ) {
            console.log(
                `[ODIN] Finished instrument pagination at ${allInstruments.length} instruments`
            );

            break;
        }

        cursor =
            nextCursor;
    }

    return allInstruments;
}

function getInstrumentAttributes(
    instrument
) {
    if (
        instrument &&
        instrument.attributes &&
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
    const metadata = 
        instrument?.event_details
            ?.metaData;

    if (
        metadata &&
        typeof metadata ===
            "object"
    ) {
        return metadata;
    }

    return {};
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

    const operatorCandidates = [
        instrument?.STRIKE_OPERATOR,
        instrument?.strike_operator,

        attributes?.STRIKE_OPERATOR,
        attributes?.strike_operator,

        metadata?.STRIKE_OPERATOR,
        metadata?.strike_operator
    ];

    for (
        const candidate of
            operatorCandidates
    ) {
        if (
            candidate !==
                undefined &&
            candidate !== null
        ) {
            return String(
                candidate
            ).trim();
        }
    }

    return null;
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

    const indexCandidates = [
        instrument?.STRIKE_INDEX,
        instrument?.strike_index,

        attributes?.STRIKE_INDEX,
        attributes?.strike_index,

        metadata?.STRIKE_INDEX,
        metadata?.strike_index
    ];

    for (
        const candidate of
            indexCandidates
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

function getInstrumentText(
    instrument
) {
    return JSON.stringify(
        instrument || {}
    ).toUpperCase();
}

function isDigitalCurrencyInstrument(
    instrument
) {
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
        productType ===
            "DIGITAL_CURRENCIES" ||
        detailProductType ===
            "DIGITAL_CURRENCIES"
    );
}

function isBTCStrikeInstrument(
    instrument
) {
    if (!instrument) {
        return false;
    }

    const text =
        getInstrumentText(
            instrument
        );

    const symbol =
        String(
            instrument.symbol ||
                ""
        ).toUpperCase();

    const displayName =
        String(
            instrument.display_name ||
                ""
        ).toUpperCase();

    const underlying =
        String(
            instrument.underlying_symbol ||
                ""
        ).toUpperCase();

    const baseCurrency =
        String(
            instrument.base_ccy ||
                ""
        ).toUpperCase();

    const eventName =
        String(
            instrument.event_details
                ?.eventName ||
                ""
        ).toUpperCase();

    const eventCode =
        String(
            instrument.event_details
                ?.eventCode ||
                ""
        ).toUpperCase();

    const metadata =
        getEventMetadata(
            instrument
        );

    const metadataText =
        JSON.stringify(
            metadata
        ).toUpperCase();

    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const attributesText =
        JSON.stringify(
            attributes
        ).toUpperCase();

    if (
        !isDigitalCurrencyInstrument(
            instrument
        )
    ) {
        return false;
    }

    const directBTC =
        underlying.includes("BTC") ||
        symbol.includes("BTC") ||
        displayName.includes("BTC") ||
        baseCurrency === "BTC" ||
        eventName.includes("BTC") ||
        eventCode.includes("BTC") ||
        metadataText.includes("BTC") ||
        attributesText.includes("BTC");

    const bitcoinPatterns = [
        "BTCUSD",
        "BTC-USD",
        "BTC/USD",
        "XBTUSD",
        "XBT-USD",
        "XBT/USD",
        "BITCOIN"
    ];

    const alternateBTC =
        bitcoinPatterns.some(
            (pattern) =>
                text.includes(
                    pattern
                )
        );

    if (
        !directBTC &&
        !alternateBTC
    ) {
        return false;
    }

    const operator =
        getStrikeOperator(
            instrument
        );

    /*
     * Strike Options currently expose the
     * comparison operator in display_name,
     * for example:
     *
     * "BITCOIN >73000 (4AM)"
     *
     * The DCM instrument payload may not provide
     * STRIKE_OPERATOR as a separate field.
     */

    const displayOperatorMatch =
        displayName.match(
            /(?:BITCOIN|BTC)\s*([<>]=?|=)/
        );

    const detectedOperator =
        operator ||
        (
            displayOperatorMatch
                ? displayOperatorMatch[1]
                : null
        );

    return (
        detectedOperator === ">" ||
        detectedOperator === ">=" ||
        detectedOperator === "<" ||
        detectedOperator === "<=" ||
        detectedOperator === "="
    );
}

function extractStrikePrice(
    instrument
) {
    if (!instrument) {
        return null;
    }

    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const metadata =
        getEventMetadata(
            instrument
        );

    const candidates = [
        instrument?.strike_price,
        instrument?.strikePrice,
        instrument?.STRIKE_PRICE,

        attributes?.strike_price,
        attributes?.strikePrice,
        attributes?.STRIKE_PRICE,

        metadata?.strike_price,
        metadata?.strikePrice,
        metadata?.STRIKE_PRICE
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
                null &&
            value > 0
        ) {
            return value;
        }
    }

    const text =
        [
            instrument.display_name,
            instrument.symbol,
            instrument.underlying_symbol
        ]
            .filter(Boolean)
            .join(" ")
            .toUpperCase();

    const dollarPatterns = [
        /\$([0-9][0-9,]*(?:\.[0-9]+)?)/,
        /USD\s*([0-9][0-9,]*(?:\.[0-9]+)?)/,
        /STRIKE[^0-9]*([0-9][0-9,]*(?:\.[0-9]+)?)/,
        /([0-9][0-9,]*(?:\.[0-9]+)?)\s*USD/
    ];

    for (
        const pattern of
            dollarPatterns
    ) {
        const match =
            text.match(
                pattern
            );

        if (match) {
            const parsed =
                safeNumber(
                    match[1].replace(
                        /,/g,
                        ""
                    )
                );

            if (
                parsed !==
                    null &&
                parsed > 0
            ) {
                return parsed;
            }
        }
    }

    /*
     * Crypto.com's Strike Option display names can expose the
     * strike directly without a dollar sign, for example:
     *
     * "BITCOIN >73000 (4AM)"
     */

    const displayName =
        String(
            instrument.display_name ||
                ""
        ).toUpperCase();

    const displayStrikeMatch =
        displayName.match(
            /(?:BITCOIN|BTC|XBT)\s*[<>]=?\s*\$?([0-9][0-9,]*(?:\.[0-9]+)?)/
        );

    if (
        displayStrikeMatch
    ) {
        const parsed =
            safeNumber(
                displayStrikeMatch[1]
                    .replace(
                        /,/g,
                        ""
                    )
            );

        if (
            parsed !== null &&
            parsed >= 10000 &&
            parsed <= 1000000
        ) {
            return parsed;
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

    for (const candidate of candidates) {
        if (
            candidate !==
                undefined &&
            candidate !== null
        ) {
            return String(
                candidate
            ).trim().toUpperCase();
        }
    }

    return null;
}

function normalizeTimeValue(
    value
) {
    const numeric =
        safeNumber(value);

    if (numeric === null) {
        return null;
    }

    if (numeric < 100000000000) {
        return numeric * 1000;
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

    for (const openValue of openCandidates) {
        for (const closeValue of closeCandidates) {
            const openTime =
                normalizeTimeValue(
                    openValue
                );

            const closeTime =
                normalizeTimeValue(
                    closeValue
                );

            if (
                openTime !== null &&
                closeTime !== null
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
        expiry - now() <=
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
                (instrument) =>
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
                    ) > currentTime
            )
            .map(
                (instrument) => ({
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
            withStrikes
                .sort(
                    (a, b) => {
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
                (a, b) =>
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
                (instrument) =>
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
                    (instrument) => {
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
                    .slice(0, 10)
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

                            baseCcy:
                                instrument.base_ccy,

                            quoteCcy:
                                instrument.quote_ccy,

                            productType:
                                instrument.product_type,

                            detailProductType:
                                instrument.detail_product_type,

                            securityType:
                                instrument.security_type,

                            securitySubType:
                                instrument.security_sub_type,

                            expiry:
                                instrument.expiry_timestamp_ms,

                            tradable:
                                instrument.tradable,

                            strikeOperator:
                                getStrikeOperator(
                                    instrument
                                ),

                            strikeIndex:
                                getStrikeIndex(
                                    instrument
                                )
                        })
                    );

            console.log(
                "[ODIN] DIGITAL CURRENCY DIAGNOSTIC SAMPLE:",
                JSON.stringify(
                    sample,
                    null,
                    2
                )
            );
        }

        instruments =
            btcFifteenMinuteInstruments;

        const lockedSymbol =
            currentRound?.symbol;

        if (
            lockedSymbol
        ) {
            const lockedInstrument =
                instruments.find(
                    (instrument) =>
                        instrument.symbol ===
                            lockedSymbol &&
                        safeNumber(
                            instrument.expiry_timestamp_ms
                        ) !== null &&
                        safeNumber(
                            instrument.expiry_timestamp_ms
                        ) > now()
                );

            if (
                lockedInstrument
            ) {
                currentContract = {
                    instrument:
                        lockedInstrument,

                    strike:
                        extractStrikePrice(
                            lockedInstrument
                        ),

                    strikeIndex:
                        getStrikeIndex(
                            lockedInstrument
                        ),

                    operator:
                        getStrikeOperator(
                            lockedInstrument
                        )
                };
            }
        }

        if (
            !currentContract ||
            currentContract.instrument?.symbol !==
                lockedSymbol
        ) {
            currentContract =
                selectCurrentContract(
                    instruments
                );
        }

        if (
            currentContract
        ) {
            console.log(
                `[ODIN] Selected BTC contract: ${currentContract.instrument.symbol}`
            );
        } else {
            console.log(
                "[ODIN] No current BTC Strike contract selected"
            );
        }

        if (
            instruments.length ===
                0 &&
            now() -
                lastNoContractLog >
                30000
        ) {
            lastNoContractLog =
                now();

            console.log(
                "[ODIN] Loaded 0 BTC Strike instruments"
            );
        }

        if (
            currentContract
        ) {
            const instrument =
                currentContract.instrument;

            state.contractSymbol =
                instrument.symbol ||
                null;

            state.contractExpiry =
                safeNumber(
                    instrument.expiry_timestamp_ms
                );

            state.strikePrice =
                currentContract.strike;

            state.strikeDistance =
                state.btcPrice !==
                    null &&
                state.strikePrice !==
                    null
                    ? state.btcPrice -
                        state.strikePrice
                    : null;

            state.strikeDistancePct =
                state.btcPrice !==
                    null &&
                state.strikePrice !==
                    null &&
                state.strikePrice !== 0
                    ? (
                          (
                              state.btcPrice -
                              state.strikePrice
                          ) /
                          state.strikePrice
                      ) *
                      100
                    : null;

            state.secondsRemaining =
                Math.max(
                    0,
                    (
                        state.contractExpiry -
                        now()
                    ) /
                        1000
                );

            state.activeRoundId =
                createRoundId(
                    state.contractExpiry
                );
        } else {
            state.contractSymbol =
                null;

            state.contractExpiry =
                null;

            state.strikePrice =
                null;

            state.strikeDistance =
                null;

            state.strikeDistancePct =
                null;

            state.secondsRemaining =
                null;

            state.activeRoundId =
                null;
        }

        state.connected =
            true;
    } catch (error) {
        state.connected =
            false;

        console.error(
            "[ODIN] Instrument refresh error:",
            error.message
        );
    } finally {
        instrumentRefreshInProgress =
            false;
    }
}

async function getContractTicker(
    contract
) {
    if (
        !contract ||
        !contract.instrument ||
        !contract.instrument.symbol
    ) {
        return null;
    }

    const result =
        await cryptoRequest(
            "public/get-tickers",
            {
                instrument_name:
                    contract.instrument
                        .symbol
            },
            CRYPTO_DCM_API
        );

    const ticker =
        result?.data?.[0];

    if (!ticker) {
        return null;
    }

    return {
        last: safeNumber(
            ticker.a
        ),

        bid: safeNumber(
            ticker.b
        ),

        ask: safeNumber(
            ticker.k
        ),

        bidSize: safeNumber(
            ticker.bs
        ),

        askSize: safeNumber(
            ticker.ks
        ),

        timestamp: safeNumber(
            ticker.t
        )
    };
}

function updatePriceHistory(
    price,
    timestamp
) {
    if (
        price === null
    ) {
        return;
    }

    priceHistory.push({
        timestamp,
        price
    });

    while (
        priceHistory.length >
        CONFIG.maxPriceHistory
    ) {
        priceHistory.shift();
    }
}

function updateTradeHistory(
    trades
) {
    if (
        !Array.isArray(trades)
    ) {
        return;
    }

    for (
        const trade of
            trades
    ) {
        const timestamp =
            safeNumber(
                trade.t
            ) || now();

        const price =
            safeNumber(
                trade.p
            );

        const quantity =
            safeNumber(
                trade.q
            );

        if (
            price === null ||
            quantity === null
        ) {
            continue;
        }

        const exists =
            tradeHistory.some(
                (item) =>
                    item.timestamp ===
                        timestamp &&
                    item.price ===
                        price &&
                    item.quantity ===
                        quantity
            );

        if (
            exists
        ) {
            continue;
        }

        tradeHistory.push({
            timestamp,
            price,
            quantity,

            side:
                trade.s ||
                null
        });
    }

    tradeHistory.sort(
        (a, b) =>
            a.timestamp -
            b.timestamp
    );

    while (
        tradeHistory.length >
        CONFIG.maxTradeHistory
    ) {
        tradeHistory.shift();
    }
}

function calculateMomentum(
    milliseconds
) {
    const cutoff =
        now() -
        milliseconds;

    const relevant =
        priceHistory.filter(
            (item) =>
                item.timestamp >=
                cutoff
        );

    if (
        relevant.length <
        2
    ) {
        return null;
    }

    const first =
        relevant[0].price;

    const last =
        relevant[
            relevant.length - 1
        ].price;

    if (
        first === null ||
        last === null ||
        first === 0
    ) {
        return null;
    }

    return (
        (
            last -
            first
        ) /
        first
    ) *
    100;
}

function calculateVolatility(
    milliseconds
) {
    const cutoff =
        now() -
        milliseconds;

    const relevant =
        priceHistory.filter(
            (item) =>
                item.timestamp >=
                cutoff
        );

    if (
        relevant.length <
        3
    ) {
        return null;
    }

    const returns = [];

    for (
        let i = 1;
        i < relevant.length;
        i++
    ) {
        const previous =
            relevant[i - 1].price;

        const current =
            relevant[i].price;

        if (
            previous === null ||
            current === null ||
            previous === 0
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

    return standardDeviation(
        returns
    );
}

function calculateVWAP(
    milliseconds
) {
    const cutoff =
        now() -
        milliseconds;

    const relevant =
        tradeHistory.filter(
            (trade) =>
                trade.timestamp >=
                cutoff
        );

    if (
        !relevant.length
    ) {
        return null;
    }

    return weightedAverage(
        relevant.map(
            (trade) => ({
                value:
                    trade.price,

                weight:
                    trade.quantity
            })
        )
    );
}

function calculateOrderBookMetrics(
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
        const bid of
            bids
    ) {
        const quantity =
            Array.isArray(bid)
                ? safeNumber(
                      bid[1]
                  )
                : safeNumber(
                      bid.q ??
                          bid.quantity
                  );

        if (
            quantity !== null
        ) {
            bidVolume +=
                quantity;
        }
    }

    for (
        const ask of
            asks
    ) {
        const quantity =
            Array.isArray(ask)
                ? safeNumber(
                      ask[1]
                  )
                : safeNumber(
                      ask.q ??
                          ask.quantity
                  );

        if (
            quantity !== null
        ) {
            askVolume +=
                quantity;
        }
    }

    const total =
        bidVolume +
        askVolume;

    if (!total) {
        return null;
    }

    return {
        bidVolume,
        askVolume,

        imbalance:
            (
                bidVolume -
                askVolume
            ) /
            total
    };
}

function calculateTradeFlow() {
    const cutoff =
        now() -
        3 *
        60 *
        1000;

    const relevant =
        tradeHistory.filter(
            (trade) =>
                trade.timestamp >=
                cutoff
        );

    let buyVolume = 0;
    let sellVolume = 0;

    for (
        const trade of
            relevant
    ) {
        if (
            String(
                trade.side ||
                    ""
            ).toUpperCase() ===
            "BUY"
        ) {
            buyVolume +=
                trade.quantity;
        } else if (
            String(
                trade.side ||
                    ""
            ).toUpperCase() ===
            "SELL"
        ) {
            sellVolume +=
                trade.quantity;
        }
    }

    const total =
        buyVolume +
        sellVolume;

    return {
        buyVolume,
        sellVolume,

        imbalance:
            total > 0
                ? (
                      buyVolume -
                      sellVolume
                  ) /
                  total
                : 0
    };
}

async function collectMarketData() {
    try {
        const [
            index,
            perp,
            book,
            trades
        ] =
            await Promise.all([
                getBTCIndex(),
                getBTCPerpTicker(),
                getBTCBook(),
                getBTCTrades()
            ]);

        if (
            index &&
            index.price !==
                null
        ) {
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
            state.btcIndexAgeMs =
                null;

            state.btcIndexStale =
                true;
        }

        if (
            perp &&
            perp.last !==
                null
        ) {
            state.btcPrice =
                perp.last;
        } else if (
            index &&
            index.price !==
                null
        ) {
            state.btcPrice =
                index.price;
        }

        /*
         * Forecasting price history follows the same DCM/CDNA
         * index that determines Strike settlement. The perpetual
         * ticker remains available for microstructure diagnostics
         * but must not silently become the settlement price series.
         */
        if (
            state.btcIndexPrice !==
                null &&
            !state.btcIndexStale &&
            state.btcIndexTimestamp !==
                null
        ) {
            updatePriceHistory(
                state.btcIndexPrice,
                state.btcIndexTimestamp
            );
        }

        updateTradeHistory(
            trades
        );

        const bookMetrics =
            calculateOrderBookMetrics(
                book
            );

        if (
            bookMetrics
        ) {
            state.orderBookImbalance =
                bookMetrics.imbalance;

            orderBookHistory.push({
                timestamp:
                    now(),

                ...bookMetrics
            });

            while (
                orderBookHistory.length >
                CONFIG.maxOrderBookHistory
            ) {
                orderBookHistory.shift();
            }
        }

        const flow =
            calculateTradeFlow();

        state.tradeFlow =
            flow.imbalance;

        previousVelocity =
            state.velocity;

        if (
            previousPrice !==
                null &&
            state.btcPrice !==
                null
        ) {
            state.velocity =
                state.btcPrice -
                previousPrice;

            if (
                previousVelocity !==
                    null
            ) {
                state.acceleration =
                    state.velocity -
                    previousVelocity;
            }
        }

        previousPrice =
            state.btcPrice;

        state.lastUpdate =
            now();
    } catch (error) {
        console.error(
            "[ODIN] Market data error:",
            error.message
        );
    }
}

async function collectContractData() {
    if (!currentContract) {
        return;
    }

    try {
        const ticker =
            await getContractTicker(
                currentContract
            );

        if (!ticker) {
            return;
        }

        state.contractBid =
            ticker.bid;

        state.contractAsk =
            ticker.ask;

        if (
            ticker.bid !==
                null &&
            ticker.ask !==
                null
        ) {
            state.contractMid =
                (
                    ticker.bid +
                    ticker.ask
                ) / 2;

            state.marketProbability =
                clamp(
                    state.contractMid *
                        10,
                    0,
                    100
                );
        } else {
            state.contractMid =
                ticker.last;

            state.marketProbability =
                ticker.last !==
                null
                    ? clamp(
                          ticker.last *
                              10,
                          0,
                          100
                      )
                    : null;
        }
    } catch (error) {
        console.error(
            "[ODIN] Contract ticker error:",
            error.message
        );
    }
}

function secondsSinceRoundStart() {
    if (
        !currentRound ||
        !currentRound.startedAt
    ) {
        return 0;
    }

    return Math.max(
        0,
        (
            now() -
            currentRound.startedAt
        ) /
            1000
    );
}

function calculateStateMetrics() {
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

    const referenceIndexPrice =
        state.btcIndexPrice !== null &&
        !state.btcIndexStale
            ? state.btcIndexPrice
            : null;

    if (
        referenceIndexPrice !==
            null &&
        state.strikePrice !==
            null
    ) {
        state.strikeDistance =
            referenceIndexPrice -
            state.strikePrice;

        state.strikeDistancePct =
            (
                (
                    referenceIndexPrice -
                    state.strikePrice
                ) /
                state.strikePrice
            ) *
            100;
    } else {
        state.strikeDistance =
            null;

        state.strikeDistancePct =
            null;
    }

    if (
        state.btcPrice !==
            null &&
        state.strikePrice !==
            null &&
        state.volatility3m !==
            null &&
        state.volatility3m !==
            0
    ) {
        state.distanceZScore =
            state.strikeDistancePct /
            state.volatility3m;
    } else {
        state.distanceZScore =
            null;
    }

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
                (a, b) =>
                    a + b,
                0
            ) /
            qualityParts.length
        ) *
        100;
}

function startNewRound() {
    if (
        !currentContract
    ) {
        return;
    }

    const expiry =
        safeNumber(
            currentContract.instrument
                .expiry_timestamp_ms
        );

    if (
        expiry ===
        null
    ) {
        return;
    }

    const id =
        createRoundId(
            expiry
        );

    if (
        currentRound &&
        currentRound.id ===
            id
    ) {
        return;
    }

    currentRound = {
        id,

        startedAt:
            now(),

        expiry,

        symbol:
            currentContract.instrument
                .symbol ||
            null,

        strike:
            currentContract.strike,

        strikeIndex:
            currentContract.strikeIndex,

        operator:
            currentContract.operator,

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
            null
    };

    state.activeRoundId =
        id;

    state.collectionStartedAt =
        now();

    state.phase =
        "COLLECTING";

    state.forecast =
        "WAIT";

    state.forecastProbability =
        null;

    state.forecastConfidence =
        null;

    state.forecastReason =
        null;

    console.log(
        `[ODIN] Started paper round ${id}`
    );
}

function calculateForecast() {
    if (
        !currentContract
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
            "No current 15-minute BTC Strike contract is available.";

        return;
    }

    startNewRound();

    if (
        !currentRound
    ) {
        return;
    }

    if (
        currentRound.forecastMade
    ) {
        state.forecast =
            currentRound.forecast ||
            "WAIT";

        state.forecastProbability =
            currentRound.forecastProbability;

        state.forecastConfidence =
            currentRound.confidence;

        state.forecastReason =
            currentRound.forecastReason ||
            null;

        state.phase =
            currentRound.forecast ===
                "SIT OUT"
                ? "SIT_OUT"
                : "LOCKED";

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
            "Collecting the full 3-minute data window.";

        return;
    }

    /*
     * Odin only makes the SIT OUT decision after the complete
     * collection period. The authoritative DCM index and strike
     * remain hard requirements because they define the settlement
     * reference. Individual diagnostics are optional inputs; one
     * missing diagnostic feed should not force a SIT OUT by itself.
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

    state.phase =
        "FORECASTING";

    let score = 0;
    let signalCount = 0;

    if (
        state.strikeDistancePct !==
        null
    ) {
        signalCount += 1;

        score += clamp(
            state.strikeDistancePct *
                4,
            -40,
            40
        );
    }

    if (
        state.momentum1m !==
        null
    ) {
        signalCount += 1;

        score += clamp(
            state.momentum1m *
                8,
            -20,
            20
        );
    }

    if (
        state.momentum3m !==
        null
    ) {
        signalCount += 1;

        score += clamp(
            state.momentum3m *
                4,
            -20,
            20
        );
    }

    if (
        state.momentum5m !==
        null
    ) {
        signalCount += 1;

        score += clamp(
            state.momentum5m *
                2,
            -10,
            10
        );
    }

    if (
        state.orderBookImbalance !==
        null
    ) {
        signalCount += 1;

        score += clamp(
            state.orderBookImbalance *
                20,
            -10,
            10
        );
    }

    if (
        state.tradeFlow !==
        null
    ) {
        signalCount += 1;

        score += clamp(
            state.tradeFlow *
                20,
            -10,
            10
        );
    }

    if (
        state.acceleration !==
        null
    ) {
        signalCount += 1;

        score += clamp(
            state.acceleration *
                2,
            -5,
            5
        );
    }

    if (
        state.vwap !== null &&
        state.btcPrice !== null
    ) {
        signalCount += 1;

        const vwapBias =
            (
                (
                    state.btcPrice -
                    state.vwap
                ) /
                state.vwap
            ) *
            100;

        score += clamp(
            vwapBias * 3,
            -8,
            8
        );
    }

    state.modelScore =
        score;

    const probability =
        clamp(
            50 +
                score,
            1,
            99
        );

    state.forecastProbability =
        probability;

    state.forecastConfidence =
        Math.abs(
            probability -
                50
        );

    /*
     * SIT OUT only when the completed collection window still
     * does not contain enough independent evidence, or when the
     * resulting model confidence remains below Odin's existing
     * threshold. Missing one individual diagnostic is not enough
     * by itself to force a skip.
     */
    if (
        signalCount <
            CONFIG.minimumForecastSignals ||
        state.forecastConfidence <
            CONFIG.minimumForecastConfidence
    ) {
        state.forecast =
            "SIT OUT";

        state.forecastProbability =
            probability;

        state.phase =
            "SIT_OUT";

        state.forecastReason =
            signalCount <
            CONFIG.minimumForecastSignals
                ? `SIT OUT: only ${signalCount} usable directional signals were available after the full 3-minute collection.`
                : "SIT OUT: no clear directional edge after the full 3-minute data collection.";

        currentRound.forecast =
            "SIT OUT";

        currentRound.forecastProbability =
            probability;

        currentRound.confidence =
            state.forecastConfidence;

        currentRound.forecastReason =
            state.forecastReason;

        currentRound.forecastMade =
            true;

        return;
    }

    state.forecast =
        probability >=
        50
            ? "YES"
            : "NO";

    state.forecastReason =
        "Directional evidence cleared Odin's minimum confidence threshold after the full data collection.";

    currentRound.forecast =
        state.forecast;

    currentRound.forecastProbability =
        state.forecastProbability;

    currentRound.confidence =
        state.forecastConfidence;

    currentRound.forecastReason =
        state.forecastReason;

    currentRound.forecastMade =
        true;

    state.phase =
        "FORECASTING";
}

function resolveCurrentContract() {
    if (
        !instruments.length
    ) {
        currentContract =
            null;

        return;
    }

    let selected =
        null;

    const lockedSymbol =
        currentRound?.symbol;

    if (
        lockedSymbol
    ) {
        const lockedInstrument =
            instruments.find(
                (instrument) =>
                    instrument.symbol ===
                        lockedSymbol &&
                    safeNumber(
                        instrument.expiry_timestamp_ms
                    ) !== null &&
                    safeNumber(
                        instrument.expiry_timestamp_ms
                    ) > now()
            );

        if (
            lockedInstrument
        ) {
            selected = {
                instrument:
                    lockedInstrument,

                strike:
                    extractStrikePrice(
                        lockedInstrument
                    ),

                strikeIndex:
                    getStrikeIndex(
                        lockedInstrument
                    ),

                operator:
                    getStrikeOperator(
                        lockedInstrument
                    )
            };
        }
    }

    if (!selected) {
        selected =
            selectCurrentContract(
                instruments
            );
    }

    if (
        !selected
    ) {
        currentContract =
            null;

        return;
    }

    const previousSymbol =
        currentContract?.instrument
            ?.symbol;

    currentContract =
        selected;

    const instrument =
        currentContract.instrument;

    state.contractSymbol =
        instrument.symbol ||
        null;

    state.contractExpiry =
        safeNumber(
            instrument.expiry_timestamp_ms
        );

    state.strikePrice =
        currentContract.strike;

    state.secondsRemaining =
        state.contractExpiry !==
            null
            ? Math.max(
                  0,
                  (
                      state.contractExpiry -
                      now()
                  ) /
                      1000
              )
            : null;

    if (
        previousSymbol !==
        instrument.symbol
    ) {
        console.log(
            `[ODIN] Active contract changed: ${instrument.symbol}`
        );

        currentRound =
            null;
    }

    state.activeRoundId =
        createRoundId(
            state.contractExpiry
        );

    if (
        dcmSubscribedContractSymbol !==
        instrument.symbol
    ) {
        dcmSubscribedContractSymbol =
            instrument.symbol;

        subscribeDCMMarketChannel(
            `settlement.${instrument.symbol}`
        );
    }
}

function evaluateExpiredRound() {
    if (
        !currentRound ||
        currentRound.result
    ) {
        return;
    }

    if (
        !currentRound.forecastMade
    ) {
        return;
    }

    if (
        state.secondsRemaining >
        0
    ) {
        return;
    }

    if (
        currentRound.strike ===
        null
    ) {
        return;
    }

    const settlementTimestamp =
        dcmSettlementCache &&
        dcmSettlementCache.symbol ===
            currentRound.symbol
            ? safeNumber(
                  dcmSettlementCache.timestamp
              )
            : null;

    const settlementPrice =
        dcmSettlementCache &&
        dcmSettlementCache.symbol ===
            currentRound.symbol &&
        settlementTimestamp !== null &&
        settlementTimestamp >=
            currentRound.expiry -
                5000
            ? safeNumber(
                  dcmSettlementCache.price
              )
            : null;

    const finalIndexPrice =
        state.btcIndexPrice !== null &&
        !state.btcIndexStale &&
        state.btcIndexSource ===
            "DCM_INDEX" &&
        state.btcIndexTimestamp !== null &&
        state.btcIndexTimestamp >=
            currentRound.expiry -
                CONFIG.maxIndexAgeMs
            ? state.btcIndexPrice
            : null;

    /*
     * SIT OUT is a deliberate abstention. It is recorded as PASS
     * for round history and never becomes a WIN or LOSS.
     */
    if (
        currentRound.forecast ===
        "SIT OUT"
    ) {
        currentRound.finalPrice =
            settlementPrice !== null
                ? settlementPrice
                : finalIndexPrice;

        currentRound.result =
            "PASS";

        currentRound.resolvedAt =
            now();

        currentRound.officialRecordCounted =
            false;

        const alreadyResolved =
            completedRounds.some(
                (round) =>
                    round.id ===
                    currentRound.id
            );

        if (
            alreadyResolved
        ) {
            console.log(
                `[ODIN] SIT OUT round ${currentRound.id} was already resolved; duplicate result ignored.`
            );

            currentRound =
                null;

            return;
        }

        const completedRound = {
            ...currentRound
        };

        completedRounds.push(
            completedRound
        );

        while (
            completedRounds.length >
            CONFIG.forecastHistoryLimit
        ) {
            completedRounds.shift();
        }

        savePersistentRecords();

        console.log(
            `[ODIN] Round ${currentRound.id} resolved: PASS (SIT OUT)`
        );

        currentRound =
            null;

        state.forecast =
            "WAIT";

        state.forecastProbability =
            null;

        state.forecastConfidence =
            null;

        state.forecastReason =
            null;

        state.activeRoundId =
            null;

        return;
    }

    const finalPrice =
        settlementPrice !== null
            ? settlementPrice
            : finalIndexPrice;

    if (
        finalPrice === null
    ) {
        console.log(
            `[ODIN] Round ${currentRound.id} not resolved: authoritative DCM settlement/index value unavailable.`
        );

        return;
    }

    const above =
        finalPrice >
        currentRound.strike;

    let result =
        "UNKNOWN";

    if (
        currentRound.forecast ===
        "YES"
    ) {
        result =
            above
                ? "WIN"
                : "LOSS";
    } else if (
        currentRound.forecast ===
        "NO"
    ) {
        result =
            above
                ? "LOSS"
                : "WIN";
    } else {
        result =
            "PASS";
    }

    currentRound.finalPrice =
        finalPrice;

    currentRound.result =
        result;

    currentRound.resolvedAt =
        now();

    const alreadyResolved =
        completedRounds.some(
            (round) =>
                round.id ===
                currentRound.id
        );

    if (
        alreadyResolved
    ) {
        console.log(
            `[ODIN] Round ${currentRound.id} was already resolved; duplicate result ignored.`
        );

        currentRound =
            null;

        return;
    }

    const completedRound = {
        ...currentRound
    };

    recordOfficialResult(
        completedRound
    );

    completedRounds.push(
        completedRound
    );

    while (
        completedRounds.length >
        CONFIG.forecastHistoryLimit
    ) {
        completedRounds.shift();
    }

    savePersistentRecords();

    console.log(
        `[ODIN] Round ${currentRound.id} resolved: ${result}`
    );

    currentRound =
        null;

    state.forecast =
        "WAIT";

    state.forecastProbability =
        null;

    state.forecastConfidence =
        null;

    state.forecastReason =
        null;

    state.activeRoundId =
        null;
}

function getPerformance() {
    updateDailyState();

    const record =
        getDailyRecord(
            getDailyDisplayDateKey()
        );

    if (
        !state.officialRecordEligible
    ) {
        return {
            wins: 0,
            losses: 0,
            total: 0,
            accuracy: null,
            date: state.recordDate,
            eligible: false
        };
    }

    return {
        wins: record.wins,
        losses: record.losses,
        total: record.total,

        accuracy:
            record.total > 0
                ? (
                      record.wins /
                      record.total
                  ) *
                  100
                : null,

        date:
            state.recordDate,

        eligible: true
    };
}

function serializeState() {
    resetDailyDisplayIfNeeded();
    updateDailyState();

    return {
        ...state,

        contractExpiryISO:
            formatTimestamp(
                state.contractExpiry
            ),

        contractExpiryMs:
            state.contractExpiry,

        roundEndsAtISO:
            formatTimestamp(
                state.contractExpiry
            ),

        collectionElapsed:
            currentRound
                ? secondsSinceRoundStart()
                : 0,

        collectionRemaining:
            currentRound
                ? Math.max(
                      0,
                      CONFIG.collectionSeconds -
                          secondsSinceRoundStart()
                  )
                : 0,

        roundRemaining:
            state.secondsRemaining !==
            null
                ? Math.max(
                      0,
                      state.secondsRemaining
                  )
                : null,

        performance:
            getPerformance(),

        recentRounds:
            completedRounds
                .slice(-20)
                .reverse()
    };
}

async function poll() {
    if (
        pollInProgress
    ) {
        return;
    }

    pollInProgress =
        true;

    try {
        const currentTime =
            now();

        if (
            currentTime -
                lastInstrumentRefresh >=
            CONFIG.instrumentRefreshMs
        ) {
            lastInstrumentRefresh =
                currentTime;

            await refreshInstruments();
        }

        await collectMarketData();

        resolveCurrentContract();

        await collectContractData();

        calculateStateMetrics();

        calculateForecast();

        evaluateExpiredRound();

        state.serverTime =
            now();

        io.emit(
            "odin:update",
            serializeState()
        );
    } finally {
        pollInProgress =
            false;
    }
}

app.get(
    "/",
    (req, res) => {
        res.sendFile(
            path.join(
                __dirname,
                "public",
                "index.html"
            )
        );
    }
);

app.use(
    express.static(
        path.join(
            __dirname,
            "public"
        )
    )
);

app.get(
    "/api/status",
    (req, res) => {
        res.json(
            serializeState()
        );
    }
);

app.get(
    "/api/history",
    (req, res) => {
        res.json({
            rounds:
                completedRounds,

            performance:
                getPerformance(),

            dailyRecords
        });
    }
);

app.get(
    "/api/instruments",
    (req, res) => {
        res.json({
            count:
                instruments.length,

            instruments:
                instruments
                    .map(
                        normalizeInstrument
                    )
                    .sort(
                        (a, b) =>
                            a.expiry -
                            b.expiry
                    )
        });
    }
);

app.get(
    "/api/instruments/raw",
    (req, res) => {
        res.json({
            count:
                rawBinaryInstruments.length,

            instruments:
                rawBinaryInstruments
        });
    }
);

app.get(
    "/api/health",
    (req, res) => {
        res.json({
            status:
                "online",

            service:
                "ODIN",

            connected:
                state.connected,

            time:
                new Date().toISOString()
        });
    }
);

io.on(
    "connection",
    (socket) => {
        console.log(
            `[ODIN] Dashboard connected: ${socket.id}`
        );

        socket.emit(
            "odin:update",
            serializeState()
        );

        socket.on(
            "disconnect",
            () => {
                console.log(
                    `[ODIN] Dashboard disconnected: ${socket.id}`
                );
            }
        );
    }
);

server.listen(
    PORT,
    async () => {
        console.log("");

        console.log(
            "=========================================="
        );

        console.log(
            "          ODIN STRIKE OPTIONS BOT"
        );

        console.log(
            "=========================================="
        );

        console.log(
            `Server: http://localhost:${PORT}`
        );

        console.log(
            "Mode: PAPER FORECASTING"
        );

        console.log(
            "Market: BTC Strike Options"
        );

        console.log(
            "Collection phase: 3 minutes"
        );

        console.log(
            "=========================================="
        );

        console.log("");

        loadPersistentRecords();
        updateDailyState();

        console.log(
            `[ODIN] Official record start date: ${CONFIG.officialRecordStartDate} ET`
        );

        connectDCMMarketSocket();

        await refreshInstruments();

        /*
         * The initial instrument refresh has now completed.
         * Start the refresh timer from this point so the first
         * poll does not immediately download all instruments again.
         */

        lastInstrumentRefresh =
            now();

        setInterval(
            async () => {
                try {
                    await poll();
                } catch (error) {
                    console.error(
                        "[ODIN] Poll error:",
                        error.message
                    );
                }
            },
            CONFIG.pollIntervalMs
        );
    }
);