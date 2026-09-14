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
    const number =
        Number(value);

    if (!Number.isFinite(number)) {
        return null;
    }

    return number;
}

function clamp(
    value,
    min,
    max
) {
    return Math.max(
        min,
        Math.min(
            max,
            value
        )
    );
}

function average(values) {
    const clean =
        values.filter(
            Number.isFinite
        );

    if (!clean.length) {
        return null;
    }

    return (
        clean.reduce(
            (a, b) =>
                a + b,
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
    dcmMarketSocket = null;
    return;
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
            price:
                safeNumber(
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
            price:
                safeNumber(
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
        last:
            safeNumber(
                ticker.a
            ),

        bid:
            safeNumber(
                ticker.b
            ),

        ask:
            safeNumber(
                ticker.k
            ),

        bidSize:
            safeNumber(
                ticker.bs
            ),

        askSize:
            safeNumber(
                ticker.ks
            ),

        volume:
            safeNumber(
                ticker.v
            ),

        timestamp:
            safeNumber(
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

    return (
        result?.data ||
        []
    );
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
            candidate !==
                null
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

function selectCurrentContract(candidates) {
    const currentTime = Date.now();

    const valid = (candidates || [])
        .filter(contract => contract)
        .filter(contract => isFifteenMinuteStrikeInstrument(contract))
        .map(contract => {
            const expiry =
                safeNumber(
                    contract.expiryTimestamp
                ) ??
                safeNumber(
                    contract.expiry_timestamp_ms
                );

            const strike =
                safeNumber(
                    contract.strike
                ) ??
                extractStrikePrice(
                    contract
                );

            return {
                instrument: contract,
                expiry,
                strike,
                strikeIndex: getStrikeIndex(contract),
                operator: getStrikeOperator(contract)
            };
        })
        .filter(contract =>
            contract.expiry !== null &&
            contract.expiry > currentTime
        );

    if (!valid.length) {
        return null;
    }

    const nearestExpiry = Math.min(
        ...valid.map(
            contract =>
                contract.expiry
        )
    );

    const sameExpiry =
        valid.filter(
            contract =>
                contract.expiry ===
                nearestExpiry
        );

    const referencePrice =
        safeNumber(
            state.btcIndexPrice ??
            state.btcPrice
        );

    sameExpiry.sort(
        (a, b) => {
            if (
                referencePrice !== null &&
                a.strike !== null &&
                b.strike !== null
            ) {
                const distanceA =
                    Math.abs(
                        a.strike -
                        referencePrice
                    );

                const distanceB =
                    Math.abs(
                        b.strike -
                        referencePrice
                    );

                if (
                    distanceA !==
                    distanceB
                ) {
                    return (
                        distanceA -
                        distanceB
                    );
                }
            }

            const aStrikeIndex =
                safeNumber(
                    a.strikeIndex
                );

            const bStrikeIndex =
                safeNumber(
                    b.strikeIndex
                );

            if (
                aStrikeIndex !== null &&
                bStrikeIndex !== null &&
                aStrikeIndex !==
                bStrikeIndex
            ) {
                return (
                    aStrikeIndex -
                    bStrikeIndex
                );
            }

            return String(
                a.instrument?.symbol ||
                ''
            ).localeCompare(
                String(
                    b.instrument?.symbol ||
                    ''
                )
            );
        }
    );

    return sameExpiry[0] || null;
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
         * rejecting them, inspect period/open/close metadata.
         */
        if (
            btcInstruments.length >
                0 &&
            btcFifteenMinuteInstruments.length ===
                0
        ) {
            const durationDiagnostic =
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

                                expiry:
                                    instrument.expiry_timestamp_ms,

                                periodCode:
                                    getPeriodCode(
                                        instrument
                                    ),

                                openTime:
                                    attributes.OPEN_TIME ||
                                    attributes.open_time ||
                                    metadata.OPEN_TIME ||
                                    metadata.open_time ||
                                    null,

                                closeTime:
                                    attributes.CLOSE_TIME ||
                                    attributes.close_time ||
                                    metadata.CLOSE_TIME ||
                                    metadata.close_time ||
                                    null,

                                attributes,
                                metadata
                            };
                        }
                    );

            console.log(
                "[ODIN] BTC duration diagnostic sample:",
                JSON.stringify(
                    durationDiagnostic,
                    null,
                    2
                )
            );
        }

        instruments =
            btcFifteenMinuteInstruments.map(
                normalizeInstrument
            );

        const selected =
            selectCurrentContract(
                btcFifteenMinuteInstruments
            );

        if (
            selected
        ) {
            const previousSymbol =
                currentContract
                    ?.instrument
                    ?.symbol ||
                null;

            currentContract =
                selected;

            if (
                previousSymbol &&
                previousSymbol !==
                    selected.instrument.symbol
            ) {
                console.log(
                    `[ODIN] Contract changed: ${previousSymbol} -> ${selected.instrument.symbol}`
                );

                currentRound =
                    null;
            }

            state.contractSymbol =
                selected.instrument.symbol ||
                null;

            state.contractExpiry =
                selected.expiry ||
                null;

            state.strikePrice =
                selected.strike ||
                null;

            state.activeRoundId =
                createRoundId(
                    selected.expiry
                );

            state.secondsRemaining =
                Math.max(
                    0,
                    Math.floor(
                        (
                            selected.expiry -
                            now()
                        ) /
                        1000
                    )
                );

            dcmSubscribedContractSymbol =
                selected.instrument.symbol ||
                null;

            if (
                dcmMarketSocket &&
                dcmMarketSocket.readyState ===
                    1 &&
                dcmSubscribedContractSymbol
            ) {
                subscribeDCMMarketChannel(
                    `settlement.${dcmSubscribedContractSymbol}`
                );
            }
        } else {
            currentContract =
                null;

            state.contractSymbol =
                null;

            state.contractExpiry =
                null;

            state.strikePrice =
                null;

            state.secondsRemaining =
                null;

            state.activeRoundId =
                null;

            dcmSubscribedContractSymbol =
                null;

            if (
                now() -
                    lastNoContractLog >
                30000
            ) {
                console.log(
                    "[ODIN] No active BTC 15-minute Strike Option contract found."
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

function resolveCurrentContract() {
    if (
        currentRound &&
        currentRound.symbol
    ) {
        const locked =
            rawBinaryInstruments.find(
                (
                    instrument
                ) =>
                    instrument.symbol ===
                    currentRound.symbol &&
                    safeNumber(
                        instrument.expiry_timestamp_ms
                    ) !== null &&
                    safeNumber(
                        instrument.expiry_timestamp_ms
                    ) >
                        now()
            );

        if (
            locked
        ) {
            currentContract = {
                instrument:
                    locked,

                expiry:
                    safeNumber(
                        locked.expiry_timestamp_ms
                    ),

                strike:
                    extractStrikePrice(
                        locked
                    ),

                strikeIndex:
                    getStrikeIndex(
                        locked
                    ),

                operator:
                    getStrikeOperator(
                        locked
                    )
            };

            state.contractSymbol =
                locked.symbol ||
                null;

            state.contractExpiry =
                currentContract.expiry ||
                null;

            state.strikePrice =
                currentContract.strike ||
                null;

            state.secondsRemaining =
                Math.max(
                    0,
                    Math.floor(
                        (
                            currentContract.expiry -
                            now()
                        ) /
                        1000
                    )
                );

            state.activeRoundId =
                createRoundId(
                    currentContract.expiry
                );

            return;
        }
    }

    if (
        !currentContract ||
        !currentContract.instrument
    ) {
        const selected =
            selectCurrentContract(
                rawBinaryInstruments
            );

        if (
            selected
        ) {
            currentContract =
                selected;
        }
    }

    if (
        !currentContract
    ) {
        return;
    }

    const expiry =
        safeNumber(
            currentContract.expiry
        );

    if (
        expiry ===
            null ||
        expiry <=
            now()
    ) {
        currentContract =
            null;

        state.contractSymbol =
            null;

        state.contractExpiry =
            null;

        state.strikePrice =
            null;

        state.secondsRemaining =
            null;

        state.activeRoundId =
            null;

        return;
    }

    state.contractSymbol =
        currentContract.instrument
            ?.symbol ||
        null;

    state.contractExpiry =
        expiry;

    state.strikePrice =
        safeNumber(
            currentContract.strike
        );

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

    state.activeRoundId =
        createRoundId(
            expiry
        );

    dcmSubscribedContractSymbol =
        currentContract.instrument
            ?.symbol ||
        null;

    if (
        dcmMarketSocket &&
        dcmMarketSocket.readyState ===
            1 &&
        dcmSubscribedContractSymbol
    ) {
        subscribeDCMMarketChannel(
            `settlement.${dcmSubscribedContractSymbol}`
        );
    }
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

        if (
            state.btcPrice !==
                null &&
            previousPrice !==
                null
        ) {
            state.velocity =
                state.btcPrice -
                previousPrice;
        } else {
            state.velocity =
                null;
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
        } else {
            state.acceleration =
                null;
        }

        previousVelocity =
            state.velocity;

        previousPrice =
            state.btcPrice;

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
            "[ODIN] Market-data collection error:",
            error.message
        );
    }
}

function startNewRound() {
    if (!currentContract) {
        return;
    }

    const expiry =
        safeNumber(
            currentContract.instrument
                ?.expiry_timestamp_ms ||
                currentContract.expiry
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
                ?.symbol ||
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

        state.forecastReason =
            "Waiting for a current BTC 15-minute Strike Option contract.";

        return;
    }

    resolveCurrentContract();

    if (
        !currentContract
    ) {
        state.phase =
            "WAITING";

        state.forecast =
            "WAIT";

        state.forecastReason =
            "Waiting for a current BTC 15-minute Strike Option contract.";

        return;
    }

    startNewRound();

    if (
        !currentRound
    ) {
        state.phase =
            "WAITING";

        state.forecast =
            "WAIT";

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
            currentRound.forecastReason;

        state.phase =
            currentRound.forecast ===
            "SIT OUT"
                ? "SIT_OUT"
                : "LOCKED";

        return;
    }

    const elapsedSeconds =
        (
            now() -
            currentRound.startedAt
        ) /
        1000;

    if (
        elapsedSeconds <
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
            `Collecting market data... ${Math.max(
                0,
                Math.ceil(
                    CONFIG.collectionSeconds -
                        elapsedSeconds
                )
            )}s remaining.`;

        return;
    }

    state.phase =
        "READY";

    /*
     * A forecast must have a fresh index and a verified strike.
     *
     * IMPORTANT:
     * The DCM index is the authoritative reference for Strike
     * Options. Do not silently substitute the Exchange index for
     * a forecast that is supposed to be evaluated against the
     * Strike Option's underlying.
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

    const signals = [];

    if (
        state.strikeDistancePct !==
            null
    ) {
        signals.push({
            name:
                "strikeDistance",

            value:
                state.strikeDistancePct,

            weight:
                4
        });
    }

    if (
        state.momentum1m !==
            null
    ) {
        signals.push({
            name:
                "momentum1m",

            value:
                state.momentum1m,

            weight:
                8
        });
    }

    if (
        state.momentum3m !==
            null
    ) {
        signals.push({
            name:
                "momentum3m",

            value:
                state.momentum3m,

            weight:
                4
        });
    }

    if (
        state.momentum5m !==
            null
    ) {
        signals.push({
            name:
                "momentum5m",

            value:
                state.momentum5m,

            weight:
                2
        });
    }

    if (
        state.orderBookImbalance !==
            null
    ) {
        signals.push({
            name:
                "orderBook",

            value:
                state.orderBookImbalance,

            weight:
                20
        });
    }

    if (
        state.tradeFlow !==
            null
    ) {
        signals.push({
            name:
                "tradeFlow",

            value:
                state.tradeFlow,

            weight:
                20
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
                state.acceleration,

            weight:
                2
        });
    }

    let score =
        0;

    if (
        state.strikeDistancePct !==
            null
    ) {
        score +=
            state.strikeDistancePct *
            4;
    }

    if (
        state.momentum1m !==
            null
    ) {
        score +=
            state.momentum1m *
            8;
    }

    if (
        state.momentum3m !==
            null
    ) {
        score +=
            state.momentum3m *
            4;
    }

    if (
        state.momentum5m !==
            null
    ) {
        score +=
            state.momentum5m *
            2;
    }

    if (
        state.orderBookImbalance !==
            null
    ) {
        score +=
            state.orderBookImbalance *
            20;
    }

    if (
        state.tradeFlow !==
            null
    ) {
        score +=
            state.tradeFlow *
            20;
    }

    if (
        state.acceleration !==
            null
    ) {
        score +=
            state.acceleration *
            2;
    }

    if (
        state.vwap !==
            null &&
        state.btcIndexPrice !==
            null
    ) {
        const vwapBias =
            calculateReturns(
                state.btcIndexPrice,
                state.vwap
            );

        if (
            vwapBias !==
            null
        ) {
            score +=
                vwapBias *
                3;
        }
    }

    state.modelScore =
        score;

    const signalCount =
        signals.length;

    const probability =
        clamp(
            50 +
                score,
            1,
            99
        );

    const confidence =
        Math.abs(
            probability -
                50
        );

    state.forecastProbability =
        probability;

    state.forecastConfidence =
        confidence;

    if (
        signalCount <
            CONFIG.minimumForecastSignals ||
        confidence <
            CONFIG.minimumForecastConfidence
    ) {
        state.phase =
            "SIT_OUT";

        state.forecast =
            "SIT OUT";

        state.forecastReason =
            "SIT OUT: The collected directional evidence did not clear Odin's minimum confidence requirement.";

        currentRound.forecast =
            "SIT OUT";

        currentRound.forecastProbability =
            probability;

        currentRound.confidence =
            confidence;

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

    state.phase =
        "LOCKED";

    state.forecastReason =
        "Directional evidence cleared Odin's minimum confidence threshold after the full data collection.";

    currentRound.forecast =
        state.forecast;

    currentRound.forecastProbability =
        probability;

    currentRound.confidence =
        confidence;

    currentRound.forecastReason =
        state.forecastReason;

    currentRound.forecastMade =
        true;

    console.log(
        `[ODIN] Paper forecast ${state.forecast} | probability ${probability.toFixed(
            1
        )}% | confidence ${confidence.toFixed(
            1
        )}% | score ${score.toFixed(
            3
        )}`
    );
}

function updateContractState() {
    resolveCurrentContract();

    if (
        !currentContract
    ) {
        state.secondsRemaining =
            null;

        return;
    }

    const expiry =
        safeNumber(
            currentContract.expiry
        );

    if (
        expiry ===
            null
    ) {
        state.secondsRemaining =
            null;

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

    state.contractBid =
        safeNumber(
            currentContract.bid
        );

    state.contractAsk =
        safeNumber(
            currentContract.ask
        );

    state.contractMid =
        safeNumber(
            currentContract.mid
        );

    if (
        state.contractMid !==
            null
    ) {
        state.marketProbability =
            clamp(
                state.contractMid *
                    10,
                0,
                100
            );
    } else {
        state.marketProbability =
            null;
    }
}

function buildPublicState() {
    return {
        ...state,

        serverTime:
            now(),

        contractExpiry:
            state.contractExpiry
                ? formatTimestamp(
                      state.contractExpiry
                  )
                : null,

        collectionStartedAt:
            state.collectionStartedAt
                ? formatTimestamp(
                      state.collectionStartedAt
                  )
                : null,

        lastUpdate:
            state.lastUpdate
                ? formatTimestamp(
                      state.lastUpdate
                  )
                : null
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