const path = require("path");
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
    underlyingIndex: "BTCUSD-INDEX",
    underlyingPerp: "BTCUSD-PERP",

    collectionSeconds: 180,

    pollIntervalMs: 1000,
    instrumentRefreshMs: 15000,

    contractSelectionHorizonMs:
        14 *
        24 *
        60 *
        60 *
        1000,

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

    activeRoundId: null
};

const priceHistory = [];
const tradeHistory = [];
const orderBookHistory = [];

const completedRounds = [];

let instruments = [];
let currentContract = null;

let lastInstrumentRefresh = 0;
let lastPoll = 0;

let previousVelocity = null;
let previousPrice = null;

let currentRound = null;

let lastNoContractLog = 0;

let rawBinaryInstruments = [];

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

async function getBTCIndex() {
    const result =
        await cryptoRequest(
            "public/get-valuations",
            {
                instrument_name:
                    CONFIG.underlyingIndex,

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

        timestamp: safeNumber(
            item.t
        )
    };
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

    return result;
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
        metadata?.strike_operator,
        metadata?.strikeOperator,
        metadata?.operator
    ];

    for (
        const value of
            operatorCandidates
    ) {
        if (
            value !== undefined &&
            value !== null
        ) {
            const operator =
                String(value).trim();

            if (
                operator === ">" ||
                operator === ">=" ||
                operator === "<" ||
                operator === "<=" ||
                operator === "=" ||
                operator === "to"
            ) {
                return operator;
            }
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

    const candidates = [
        instrument?.STRIKE_INDEX,
        instrument?.strike_index,

        attributes?.STRIKE_INDEX,
        attributes?.strike_index
    ];

    for (
        const value of candidates
    ) {
        if (
            value !== undefined &&
            value !== null &&
            String(value).trim() !== ""
        ) {
            return String(
                value
            ).trim();
        }
    }

    return null;
}

function parseCryptoDateTime(
    value
) {
    if (!value) {
        return null;
    }

    const text =
        String(value).trim();

    if (
        /^\d{8}-\d{2}:\d{2}:\d{2}(?:\.\d+)?$/
            .test(text)
    ) {
        const match =
            text.match(
                /^(\d{4})(\d{2})(\d{2})-(\d{2}):(\d{2}):(\d{2})(?:\.(\d+))?$/
            );

        if (match) {
            const year =
                Number(match[1]);

            const month =
                Number(match[2]);

            const day =
                Number(match[3]);

            const hour =
                Number(match[4]);

            const minute =
                Number(match[5]);

            const second =
                Number(match[6]);

            const fraction =
                match[7] || "";

            const milliseconds =
                Number(
                    (
                        fraction +
                        "000"
                    ).slice(0, 3)
                );

            const timestamp =
                Date.UTC(
                    year,
                    month - 1,
                    day,
                    hour,
                    minute,
                    second,
                    milliseconds
                );

            return Number.isFinite(
                timestamp
            )
                ? timestamp
                : null;
        }
    }

    const parsed =
        Date.parse(text);

    return Number.isFinite(parsed)
        ? parsed
        : null;
}

function getOpenTime(
    instrument
) {
    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const value =
        attributes.OPEN_TIME ||
        attributes.open_time ||
        instrument.OPEN_TIME ||
        instrument.open_time;

    return parseCryptoDateTime(
        value
    );
}

function getCloseTime(
    instrument
) {
    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const value =
        attributes.CLOSE_TIME ||
        attributes.close_time ||
        instrument.CLOSE_TIME ||
        instrument.close_time;

    return parseCryptoDateTime(
        value
    );
}

function getInstrumentText(
    instrument
) {
    try {
        return JSON.stringify(
            instrument
        ).toUpperCase();
    } catch {
        return "";
    }
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

    const securitySubType =
        String(
            instrument?.security_sub_type ||
                ""
        ).toUpperCase();

    return (
        productType ===
            "DIGITAL_CURRENCIES" ||
        detailProductType ===
            "DIGITAL_CURRENCIES" ||
        securitySubType ===
            "BINARY_OPTION"
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

    return (
        operator === ">" ||
        operator === ">=" ||
        operator === "<" ||
        operator === "<=" ||
        operator === "="
    );
}

function parseNumberFromText(
    value
) {
    if (
        value === undefined ||
        value === null
    ) {
        return null;
    }

    const direct =
        safeNumber(value);

    if (direct !== null) {
        return direct;
    }

    const text =
        String(value);

    const matches =
        text.match(
            /\$?\d+(?:,\d{3})*(?:\.\d+)?/g
        );

    if (!matches?.length) {
        return null;
    }

    const numbers =
        matches
            .map(
                (item) =>
                    Number(
                        item
                            .replace(
                                "$",
                                ""
                            )
                            .replace(
                                /,/g,
                                ""
                            )
                    )
            )
            .filter(
                Number.isFinite
            );

    if (!numbers.length) {
        return null;
    }

    return Math.max(
        ...numbers
    );
}

function extractStrikePrice(
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
        instrument?.strike_price,
        instrument?.strikePrice,
        instrument?.strike,
        instrument?.StrikePrice,
        instrument?.STRIKE_PRICE,

        attributes?.strike_price,
        attributes?.strikePrice,
        attributes?.strike,
        attributes?.StrikePrice,
        attributes?.STRIKE_PRICE,

        metadata?.strike_price,
        metadata?.strikePrice,
        metadata?.strike,
        metadata?.StrikePrice,
        metadata?.STRIKE_PRICE,

        instrument?.event_details
            ?.strike_price,

        instrument?.event_details
            ?.strikePrice,

        instrument?.event_details
            ?.strike,

        instrument?.event_details
            ?.StrikePrice
    ];

    for (
        const candidate of
            candidates
    ) {
        const parsed =
            parseNumberFromText(
                candidate
            );

        if (
            parsed !== null &&
            parsed > 0
        ) {
            return parsed;
        }
    }

    const text =
        getInstrumentText(
            instrument
        );

    const patterns = [
        /STRIKE[_\s-]*PRICE[^0-9]{0,20}(\d+(?:\.\d+)?)/i,
        /STRIKE[^0-9]{0,20}(\d{3,}(?:\.\d+)?)/i
    ];

    for (
        const pattern of patterns
    ) {
        const match =
            text.match(
                pattern
            );

        if (match) {
            const parsed =
                safeNumber(
                    match[1]
                );

            if (
                parsed !== null &&
                parsed > 0
            ) {
                return parsed;
            }
        }
    }

    return null;
}

function normalizeInstrument(
    instrument
) {
    const strikePrice =
        extractStrikePrice(
            instrument
        );

    const expiry =
        safeNumber(
            instrument?.expiry_timestamp_ms
        ) ||
        getCloseTime(
            instrument
        );

    return {
        symbol:
            instrument?.symbol ||
            null,

        displayName:
            instrument?.display_name ||
            null,

        underlying:
            instrument?.underlying_symbol ||
            null,

        baseCurrency:
            instrument?.base_ccy ||
            null,

        quoteCurrency:
            instrument?.quote_ccy ||
            null,

        productType:
            instrument?.product_type ||
            null,

        detailProductType:
            instrument?.detail_product_type ||
            null,

        securityType:
            instrument?.security_type ||
            null,

        securitySubType:
            instrument?.security_sub_type ||
            null,

        tradable:
            instrument?.tradable === true,

        strikeOperator:
            getStrikeOperator(
                instrument
            ),

        strikeIndex:
            getStrikeIndex(
                instrument
            ),

        strikePrice,

        expiry,

        expiryISO:
            formatTimestamp(
                expiry
            ),

        openTime:
            getOpenTime(
                instrument
            ),

        closeTime:
            getCloseTime(
                instrument
            ),

        periodCode:
            getInstrumentAttributes(
                instrument
            )?.PERIOD_CODE ||
            null,

        periodIndex:
            getInstrumentAttributes(
                instrument
            )?.PERIOD_INDEX ||
            null
    };
}

function getContractStrike(
    instrument
) {
    return extractStrikePrice(
        instrument
    );
}

function selectCurrentContract() {
    const currentTime =
        now();

    const eligible =
        instruments
            .filter(
                (instrument) => {
                    const normalized =
                        normalizeInstrument(
                            instrument
                        );

                    const expiry =
                        normalized.expiry;

                    if (
                        !expiry ||
                        expiry <=
                            currentTime
                    ) {
                        return false;
                    }

                    if (
                        normalized.tradable !==
                        true
                    ) {
                        return false;
                    }

                    return (
                        expiry -
                            currentTime <=
                        CONFIG.contractSelectionHorizonMs
                    );
                }
            )
            .sort(
                (a, b) => {
                    const expiryA =
                        normalizeInstrument(
                            a
                        ).expiry;

                    const expiryB =
                        normalizeInstrument(
                            b
                        ).expiry;

                    return (
                        expiryA -
                        expiryB
                    );
                }
            );

    if (!eligible.length) {
        currentContract =
            null;

        state.contractSymbol =
            null;

        state.contractExpiry =
            null;

        state.secondsRemaining =
            null;

        state.strikePrice =
            null;

        state.strikeDistance =
            null;

        state.strikeDistancePct =
            null;

        return null;
    }

    const best =
        eligible.find(
            (instrument) =>
                getContractStrike(
                    instrument
                ) !== null
        ) ||
        eligible[0];

    currentContract =
        best;

    const normalized =
        normalizeInstrument(
            best
        );

    state.contractSymbol =
        normalized.symbol;

    state.contractExpiry =
        normalized.expiry;

    state.strikePrice =
        normalized.strikePrice;

    state.secondsRemaining =
        Math.max(
            0,
            (
                normalized.expiry -
                currentTime
            ) / 1000
        );

    if (
        state.btcPrice !== null &&
        state.strikePrice !== null
    ) {
        state.strikeDistance =
            state.btcPrice -
            state.strikePrice;

        state.strikeDistancePct =
            (
                state.strikeDistance /
                state.strikePrice
            ) *
            100;
    } else {
        state.strikeDistance =
            null;

        state.strikeDistancePct =
            null;
    }

    return currentContract;
}

async function refreshInstruments() {
    try {
        const loadedInstruments =
            await getInstruments();

        rawBinaryInstruments =
            loadedInstruments;

        console.log(
            `[ODIN] DCM BINARY_OPTION instruments received: ${loadedInstruments.length}`
        );

        /*
         * First inspect how many digital-currency
         * binary options Crypto.com returned.
         */

        const digitalCurrencyInstruments =
            loadedInstruments.filter(
                isDigitalCurrencyInstrument
            );

        console.log(
            `[ODIN] Digital-currency Binary Options: ${digitalCurrencyInstruments.length}`
        );

        /*
         * Now identify BTC using all of the available
         * DCM metadata instead of assuming BTC must
         * literally be part of the symbol.
         */

        const btcInstruments =
            loadedInstruments.filter(
                isBTCStrikeInstrument
            );

        console.log(
            `[ODIN] BTC Strike candidates after DCM metadata filter: ${btcInstruments.length}`
        );

        instruments =
            btcInstruments;

        state.connected =
            true;

        const normalizedBTC =
            btcInstruments.map(
                normalizeInstrument
            );

        const withStrikes =
            normalizedBTC.filter(
                (instrument) =>
                    instrument.strikePrice !==
                    null
            );

        console.log(
            `[ODIN] BTC instruments with detected dollar strikes: ${withStrikes.length}`
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

        /*
         * Diagnostic #2:
         *
         * If BTC candidates exist but no dollar
         * strike was found, show exactly what the
         * instrument contains.
         */

        if (
            btcInstruments.length >
                0 &&
            withStrikes.length ===
                0
        ) {
            const sample =
                btcInstruments
                    .slice(0, 20)
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
                                ),

                            normalized:
                                normalizeInstrument(
                                    instrument
                                ),

                            attributes:
                                instrument.attributes,

                            eventDetails:
                                instrument.event_details
                        })
                    );

            console.log(
                "[ODIN] BTC instruments found, but no dollar strike detected:",
                JSON.stringify(
                    sample,
                    null,
                    2
                )
            );
        }

        /*
         * Diagnostic #3:
         *
         * Show BTC-like raw instruments if our filter
         * somehow misses them.
         */

        if (
            btcInstruments.length ===
                0 &&
            digitalCurrencyInstruments.length ===
                0
        ) {
            const rawBTCMatches =
                loadedInstruments.filter(
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
                `[ODIN] Raw BTC/XBT/BITCOIN matches across all Binary Options: ${rawBTCMatches.length}`
            );

            if (
                rawBTCMatches.length >
                0
            ) {
                const sample =
                    rawBTCMatches
                        .slice(0, 20)
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

                                strikeOperator:
                                    getStrikeOperator(
                                        instrument
                                    ),

                                strikeIndex:
                                    getStrikeIndex(
                                        instrument
                                    ),

                                attributes:
                                    instrument.attributes,

                                eventDetails:
                                    instrument.event_details
                            })
                        );

                console.log(
                    "[ODIN] RAW BTC-LIKE SAMPLE:",
                    JSON.stringify(
                        sample,
                        null,
                        2
                    )
                );
            }
        }

        console.log(
            `[ODIN] Loaded ${instruments.length} BTC Strike instruments`
        );
    } catch (error) {
        state.connected =
            false;

        console.error(
            "[ODIN] Instrument refresh error:",
            error.message
        );
    }
}

async function getContractTicker(
    instrument
) {
    if (!instrument?.symbol) {
        return null;
    }

    try {
        const result =
            await cryptoRequest(
                "public/get-tickers",
                {
                    instrument_name:
                        instrument.symbol
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

            volume: safeNumber(
                ticker.v
            ),

            timestamp: safeNumber(
                ticker.t
            )
        };
    } catch (error) {
        console.error(
            "[ODIN] Contract ticker error:",
            error.message
        );

        return null;
    }
}

function updatePriceHistory(
    price,
    timestamp
) {
    if (
        price === null ||
        !Number.isFinite(price)
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
    for (
        const trade of trades
    ) {
        const price =
            safeNumber(
                trade.p
            );

        const quantity =
            safeNumber(
                trade.q
            );

        const timestamp =
            safeNumber(
                trade.t
            ) ||
            now();

        if (
            price === null ||
            quantity === null
        ) {
            continue;
        }

        tradeHistory.push({
            timestamp,
            price,
            quantity,

            side:
                trade.s ||
                trade.side ||
                null
        });
    }

    while (
        tradeHistory.length >
        CONFIG.maxTradeHistory
    ) {
        tradeHistory.shift();
    }
}

function calculateOrderBookMetrics(
    book
) {
    const data =
        book?.data?.[0] ||
        book?.data ||
        book;

    const bids =
        Array.isArray(
            data?.bids
        )
            ? data.bids
            : [];

    const asks =
        Array.isArray(
            data?.asks
        )
            ? data.asks
            : [];

    const normalizedBids =
        bids
            .map(
                (level) => ({
                    price:
                        safeNumber(
                            level[0]
                        ),

                    quantity:
                        safeNumber(
                            level[1]
                        )
                })
            )
            .filter(
                (level) =>
                    level.price !==
                        null &&
                    level.quantity !==
                        null
            );

    const normalizedAsks =
        asks
            .map(
                (level) => ({
                    price:
                        safeNumber(
                            level[0]
                        ),

                    quantity:
                        safeNumber(
                            level[1]
                        )
                })
            )
            .filter(
                (level) =>
                    level.price !==
                        null &&
                    level.quantity !==
                        null
            );

    if (
        !normalizedBids.length ||
        !normalizedAsks.length
    ) {
        return null;
    }

    const bidVolume =
        normalizedBids.reduce(
            (sum, level) =>
                sum +
                level.quantity,
            0
        );

    const askVolume =
        normalizedAsks.reduce(
            (sum, level) =>
                sum +
                level.quantity,
            0
        );

    const total =
        bidVolume +
        askVolume;

    return {
        bidVolume,
        askVolume,

        imbalance:
            total > 0
                ? (
                      (
                          bidVolume -
                          askVolume
                      ) /
                      total
                  ) *
                  100
                : null,

        bestBid:
            normalizedBids[0]
                ?.price ??
            null,

        bestAsk:
            normalizedAsks[0]
                ?.price ??
            null
    };
}

function calculateTradeFlow() {
    const recent =
        tradeHistory.slice(
            -100
        );

    if (!recent.length) {
        return {
            buyVolume: 0,
            sellVolume: 0,
            imbalance: null
        };
    }

    let buyVolume = 0;
    let sellVolume = 0;

    for (
        const trade of recent
    ) {
        const side =
            String(
                trade.side ||
                    ""
            ).toLowerCase();

        if (
            side === "buy" ||
            side === "b"
        ) {
            buyVolume +=
                trade.quantity;
        } else if (
            side === "sell" ||
            side === "s"
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
                      (
                          buyVolume -
                          sellVolume
                      ) /
                      total
                  ) *
                  100
                : null
    };
}

function getPriceAtOrBefore(
    millisecondsAgo
) {
    const target =
        now() -
        millisecondsAgo;

    for (
        let i =
            priceHistory.length -
            1;
        i >= 0;
        i--
    ) {
        if (
            priceHistory[i]
                .timestamp <=
            target
        ) {
            return priceHistory[i]
                .price;
        }
    }

    return null;
}

function calculateMomentum(
    milliseconds
) {
    if (
        state.btcPrice ===
            null
    ) {
        return null;
    }

    const oldPrice =
        getPriceAtOrBefore(
            milliseconds
        );

    if (
        oldPrice === null ||
        oldPrice === 0
    ) {
        return null;
    }

    return (
        (
            state.btcPrice -
            oldPrice
        ) /
        oldPrice
    ) *
    100;
}

function calculateVolatility(
    milliseconds
) {
    const cutoff =
        now() -
        milliseconds;

    const values =
        priceHistory
            .filter(
                (item) =>
                    item.timestamp >=
                    cutoff
            )
            .map(
                (item) =>
                    item.price
            );

    if (
        values.length <
        3
    ) {
        return null;
    }

    const returns = [];

    for (
        let i = 1;
        i < values.length;
        i++
    ) {
        if (
            values[i - 1] ===
                0
        ) {
            continue;
        }

        returns.push(
            (
                (
                    values[i] -
                    values[i - 1]
                ) /
                values[i - 1]
            ) *
            100
        );
    }

    return standardDeviation(
        returns
    );
}

function calculateVWAP() {
    const recent =
        tradeHistory.slice(
            -200
        );

    if (!recent.length) {
        return null;
    }

    const items =
        recent.map(
            (trade) => ({
                value:
                    trade.price,

                weight:
                    trade.quantity
            })
        );

    return weightedAverage(
        items
    );
}

function calculateDistanceZScore() {
    if (
        state.strikeDistance ===
            null
    ) {
        return null;
    }

    const recentDistances =
        priceHistory
            .slice(-300)
            .map(
                (item) => {
                    if (
                        state.strikePrice ===
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
        recentDistances.length <
        10
    ) {
        return null;
    }

    const mean =
        average(
            recentDistances
        );

    const sd =
        standardDeviation(
            recentDistances
        );

    if (
        sd === null ||
        sd === 0
    ) {
        return 0;
    }

    return (
        state.strikeDistance -
        mean
    ) / sd;
}

function calculateStateMetrics() {
    state.momentum1m =
        calculateMomentum(
            60 * 1000
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
            60 * 1000
        );

    state.volatility3m =
        calculateVolatility(
            3 *
                60 *
                1000
        );

    state.vwap =
        calculateVWAP();

    state.distanceZScore =
        calculateDistanceZScore();

    const recentPrices =
        priceHistory.slice(
            -60
        );

    state.dataQuality =
        clamp(
            (
                recentPrices.length /
                60
            ) *
            100,
            0,
            100
        );
}

function getForecastDirectionScore() {
    let score = 0;

    if (
        state.momentum1m !==
            null
    ) {
        score +=
            clamp(
                state.momentum1m *
                    8,
                -25,
                25
            );
    }

    if (
        state.momentum3m !==
            null
    ) {
        score +=
            clamp(
                state.momentum3m *
                    5,
                -20,
                20
            );
    }

    if (
        state.momentum5m !==
            null
    ) {
        score +=
            clamp(
                state.momentum5m *
                    3,
                -15,
                15
            );
    }

    if (
        state.orderBookImbalance !==
            null
    ) {
        score +=
            clamp(
                state.orderBookImbalance *
                    0.2,
                -10,
                10
            );
    }

    if (
        state.tradeFlow !==
            null
    ) {
        score +=
            clamp(
                state.tradeFlow *
                    0.2,
                -10,
                10
            );
    }

    if (
        state.velocity !==
            null
    ) {
        score +=
            clamp(
                state.velocity /
                    20,
                -10,
                10
            );
    }

    if (
        state.acceleration !==
            null
    ) {
        score +=
            clamp(
                state.acceleration /
                    10,
                -5,
                5
            );
    }

    return clamp(
        score,
        -100,
        100
    );
}

function calculateForecast() {
    if (
        !currentContract ||
        state.strikePrice ===
            null ||
        state.btcPrice ===
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

        state.modelScore =
            0;

        return;
    }

    const seconds =
        state.secondsRemaining;

    if (
        seconds === null ||
        seconds <= 0
    ) {
        state.phase =
            "EXPIRED";

        state.forecast =
            "WAIT";

        return;
    }

    const collectionElapsed =
        currentRound
            ? secondsSinceRoundStart()
            : 0;

    if (
        collectionElapsed <
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

        state.modelScore =
            0;

        return;
    }

    const score =
        getForecastDirectionScore();

    state.modelScore =
        score;

    const distance =
        state.btcPrice -
        state.strikePrice;

    const timeFactor =
        clamp(
            1 -
                (
                    seconds /
                    180
                ),
            0,
            1
        );

    let probability =
        50 +
        score * 0.35;

    if (
        distance > 0
    ) {
        probability +=
            clamp(
                (
                    distance /
                    state.strikePrice
                ) *
                1000 *
                (
                    0.4 +
                    timeFactor
                ),
                0,
                15
            );
    } else {
        probability -=
            clamp(
                (
                    Math.abs(
                        distance
                    ) /
                    state.strikePrice
                ) *
                1000 *
                (
                    0.4 +
                    timeFactor
                ),
                0,
                15
            );
    }

    probability =
        clamp(
            probability,
            1,
            99
        );

    state.forecastProbability =
        probability;

    state.forecastConfidence =
        clamp(
            50 +
                Math.abs(
                    probability -
                        50
                ) *
                1.5,
            0,
            99
        );

    if (
        probability >=
        58
    ) {
        state.forecast =
            "YES";
    } else if (
        probability <=
        42
    ) {
        state.forecast =
            "NO";
    } else {
        state.forecast =
            "WAIT";
    }

    state.phase =
        "FORECAST";
}

function secondsSinceRoundStart() {
    if (
        !currentRound?.startedAt
    ) {
        return 0;
    }

    return Math.max(
        0,
        (
            now() -
            currentRound.startedAt
        ) / 1000
    );
}

function ensureCurrentRound() {
    if (!currentContract) {
        return;
    }

    const expiry =
        state.contractExpiry;

    if (!expiry) {
        return;
    }

    const id =
        createRoundId(
            expiry
        );

    if (
        currentRound?.id ===
        id
    ) {
        return;
    }

    currentRound = {
        id,

        symbol:
            state.contractSymbol,

        strike:
            state.strikePrice,

        expiry,

        startedAt:
            now(),

        forecast:
            null,

        forecastProbability:
            null,

        forecastMade:
            false,

        finalPrice:
            null,

        result:
            null,

        resolvedAt:
            null
    };

    state.collectionStartedAt =
        currentRound.startedAt;

    state.activeRoundId =
        id;
}

function updateRoundForecast() {
    if (
        !currentRound
    ) {
        return;
    }

    if (
        state.forecast ===
            "WAIT"
    ) {
        return;
    }

    if (
        secondsSinceRoundStart() <
        CONFIG.collectionSeconds
    ) {
        return;
    }

    if (
        currentRound.forecastMade
    ) {
        return;
    }

    currentRound.forecast =
        state.forecast;

    currentRound.forecastProbability =
        state.forecastProbability;

    currentRound.forecastMade =
        true;

    console.log(
        `[ODIN] Forecast for ${currentRound.symbol}: ${currentRound.forecast} (${currentRound.forecastProbability?.toFixed(2)}%)`
    );
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
            index?.price !==
                null &&
            index?.price !==
                undefined
        ) {
            state.btcIndexPrice =
                index.price;
        }

        if (
            perp?.last !==
                null &&
            perp?.last !==
                undefined
        ) {
            state.btcPrice =
                perp.last;
        } else if (
            index?.price !==
                null &&
            index?.price !==
                undefined
        ) {
            state.btcPrice =
                index.price;
        }

        updatePriceHistory(
            state.btcPrice,
            now()
        );

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

async function resolveCurrentContract() {
    const previousSymbol =
        currentContract?.symbol ||
        null;

    const contract =
        selectCurrentContract();

    if (!contract) {
        if (
            now() -
                lastNoContractLog >
            30000
        ) {
            console.log(
                "[ODIN] No eligible BTC Strike contract found."
            );

            lastNoContractLog =
                now();
        }

        return;
    }

    ensureCurrentRound();

    if (
        previousSymbol !==
        contract.symbol
    ) {
        console.log(
            `[ODIN] Selected contract: ${contract.symbol}`
        );

        console.log(
            `[ODIN] Strike: ${state.strikePrice ?? "N/A"} | Expiry: ${formatTimestamp(state.contractExpiry)}`
        );
    }

    if (
        state.contractExpiry !==
            null
    ) {
        state.secondsRemaining =
            Math.max(
                0,
                (
                    state.contractExpiry -
                    now()
                ) /
                1000
            );
    }

    updateRoundForecast();
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
                ) /
                2;

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
        state.btcIndexPrice ===
            null &&
        state.btcPrice ===
            null
    ) {
        return;
    }

    if (
        currentRound.strike ===
        null
    ) {
        return;
    }

    const finalPrice =
        state.btcIndexPrice !==
        null
            ? state.btcIndexPrice
            : state.btcPrice;

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

    completedRounds.push({
        ...currentRound
    });

    while (
        completedRounds.length >
        CONFIG.forecastHistoryLimit
    ) {
        completedRounds.shift();
    }

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

    state.activeRoundId =
        null;
}

function getPerformance() {
    const resolved =
        completedRounds.filter(
            (round) =>
                round.result ===
                    "WIN" ||
                round.result ===
                    "LOSS"
        );

    const wins =
        resolved.filter(
            (round) =>
                round.result ===
                "WIN"
        ).length;

    const losses =
        resolved.filter(
            (round) =>
                round.result ===
                "LOSS"
        ).length;

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
                : null
    };
}

function serializeState() {
    return {
        ...state,

        contractExpiryISO:
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

        performance:
            getPerformance(),

        recentRounds:
            completedRounds
                .slice(-20)
                .reverse()
    };
}

async function poll() {
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

    await resolveCurrentContract();

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
                getPerformance()
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

        await refreshInstruments();

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