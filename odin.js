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
    return Math.max(min, Math.min(max, value));
}

function average(values) {
    const clean = values.filter(Number.isFinite);

    if (!clean.length) {
        return null;
    }

    return clean.reduce((a, b) => a + b, 0) / clean.length;
}

function standardDeviation(values) {
    const clean = values.filter(Number.isFinite);

    if (clean.length < 2) {
        return null;
    }

    const mean = average(clean);

    const variance =
        clean.reduce((sum, value) => {
            return sum + Math.pow(value - mean, 2);
        }, 0) / clean.length;

    return Math.sqrt(variance);
}

function weightedAverage(items) {
    if (!items.length) {
        return null;
    }

    let numerator = 0;
    let denominator = 0;

    for (const item of items) {
        const value = safeNumber(item.value);
        const weight = safeNumber(item.weight);

        if (
            value === null ||
            weight === null ||
            weight <= 0
        ) {
            continue;
        }

        numerator += value * weight;
        denominator += weight;
    }

    if (!denominator) {
        return null;
    }

    return numerator / denominator;
}

function percentile(values, percentileValue) {
    const clean = values
        .filter(Number.isFinite)
        .sort((a, b) => a - b);

    if (!clean.length) {
        return null;
    }

    const index =
        (clean.length - 1) *
        percentileValue;

    const lower = Math.floor(index);
    const upper = Math.ceil(index);

    if (lower === upper) {
        return clean[lower];
    }

    return (
        clean[lower] +
        (clean[upper] - clean[lower]) *
            (index - lower)
    );
}

function formatTimestamp(timestamp) {
    if (!timestamp) {
        return null;
    }

    return new Date(timestamp).toISOString();
}

function createRoundId(expiry) {
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

    for (const [key, value] of Object.entries(params)) {
        if (
            value !== undefined &&
            value !== null &&
            value !== ""
        ) {
            url.searchParams.set(
                key,
                String(value)
            );
        }
    }

    const response = await fetch(
        url.toString(),
        {
            method: "GET",
            headers: {
                Accept: "application/json"
            }
        }
    );

    if (!response.ok) {
        throw new Error(
            `Crypto.com HTTP ${response.status}`
        );
    }

    const json = await response.json();

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
    const result = await cryptoRequest(
        "public/get-valuations",
        {
            instrument_name:
                CONFIG.underlyingIndex,
            valuation_type: "index_price",
            count: 1
        }
    );

    const item =
        result?.data?.[0];

    if (!item) {
        return null;
    }

    return {
        price: safeNumber(item.v),
        timestamp: safeNumber(item.t)
    };
}

async function getBTCPerpTicker() {
    const result = await cryptoRequest(
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
        last: safeNumber(ticker.a),
        bid: safeNumber(ticker.b),
        ask: safeNumber(ticker.k),
        bidSize: safeNumber(ticker.bs),
        askSize: safeNumber(ticker.ks),
        volume: safeNumber(ticker.v),
        timestamp: safeNumber(ticker.t)
    };
}

async function getBTCBook() {
    const result = await cryptoRequest(
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
    const result = await cryptoRequest(
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

    /*
     * Crypto.com allows up to 1000 instruments per page.
     *
     * IMPORTANT:
     * Do not stop after 10 pages.
     *
     * The previous code stopped at:
     *
     *     10 pages x 1000 = 10,000 instruments
     *
     * BTC Strike Options may exist beyond those first
     * 10,000 instruments.
     *
     * We now continue following next_cursor until the
     * API tells us there are no more pages.
     *
     * 1000 pages is only a safety limit against a bad
     * cursor/API response. It is not the normal stopping
     * condition.
     */

    for (let page = 0; page < 1000; page++) {
        const params = {
            inst_type: "BINARY_OPTION",
            limit: 1000,
            since: 0
        };

        if (cursor) {
            params.cursor = cursor;
        }

        const result =
            await cryptoRequest(
                "public/get-instruments",
                params,
                CRYPTO_DCM_API
            );

        const pageData =
            Array.isArray(result?.data)
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

        cursor = nextCursor;
    }

    return allInstruments;
}

function getInstrumentAttributes(instrument) {
    if (
        instrument &&
        instrument.attributes &&
        typeof instrument.attributes === "object"
    ) {
        return instrument.attributes;
    }

    return {};
}

function getEventMetadata(instrument) {
    const metadata =
        instrument?.event_details
            ?.metaData;

    if (
        metadata &&
        typeof metadata === "object"
    ) {
        return metadata;
    }

    return {};
}

function getStrikeOperator(instrument) {
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

    for (const value of operatorCandidates) {
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

function getStrikeIndex(instrument) {
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

    for (const value of candidates) {
        if (
            value !== undefined &&
            value !== null &&
            String(value).trim() !== ""
        ) {
            return String(value).trim();
        }
    }

    return null;
}

function getOpenTime(instrument) {
    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const value =
        attributes.OPEN_TIME ||
        attributes.open_time ||
        instrument.OPEN_TIME ||
        instrument.open_time;

    if (!value) {
        return null;
    }

    const timestamp =
        Date.parse(
            String(value)
        );

    return Number.isFinite(timestamp)
        ? timestamp
        : null;
}

function getCloseTime(instrument) {
    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const value =
        attributes.CLOSE_TIME ||
        attributes.close_time ||
        instrument.CLOSE_TIME ||
        instrument.close_time;

    if (!value) {
        return null;
    }

    const timestamp =
        Date.parse(
            String(value)
        );

    return Number.isFinite(timestamp)
        ? timestamp
        : null;
}

function isBTCStrikeInstrument(instrument) {
    if (!instrument) {
        return false;
    }

    const symbol =
        String(
            instrument.symbol || ""
        ).toUpperCase();

    const displayName =
        String(
            instrument.display_name || ""
        ).toUpperCase();

    const underlying =
        String(
            instrument.underlying_symbol || ""
        ).toUpperCase();

    const baseCurrency =
        String(
            instrument.base_ccy || ""
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

    const metadataText =
        JSON.stringify(
            getEventMetadata(
                instrument
            )
        ).toUpperCase();

    const isBTC =
        underlying.includes("BTC") ||
        symbol.includes("BTC") ||
        displayName.includes("BTC") ||
        baseCurrency === "BTC" ||
        eventName.includes("BTC") ||
        eventCode.includes("BTC") ||
        metadataText.includes("BTC");

    if (!isBTC) {
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

function parseNumberFromText(value) {
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
            .map((item) =>
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

function extractStrikePrice(instrument) {
    const possibleFields = [
        "strike_price",
        "strike",
        "STRIKE_PRICE",
        "strikePrice",
        "strike_index_price",
        "STRIKE_VALUE",
        "strike_value"
    ];

    for (const field of possibleFields) {
        if (
            instrument[field] !==
                undefined &&
            instrument[field] !== null
        ) {
            const value =
                parseNumberFromText(
                    instrument[field]
                );

            if (value !== null) {
                return value;
            }
        }
    }

    const attributes =
        getInstrumentAttributes(
            instrument
        );

    const attributeStrikeFields = [
        "STRIKE_PRICE",
        "strike_price",
        "STRIKE",
        "strike",
        "STRIKE_VALUE",
        "strike_value",
        "strikePrice"
    ];

    for (
        const field of
            attributeStrikeFields
    ) {
        if (
            attributes[field] !==
                undefined &&
            attributes[field] !== null
        ) {
            const value =
                parseNumberFromText(
                    attributes[field]
                );

            if (value !== null) {
                return value;
            }
        }
    }

    for (
        const [key, value] of
        Object.entries(attributes)
    ) {
        const normalizedKey =
            String(key)
                .toLowerCase()
                .replace(
                    /[^a-z0-9]/g,
                    ""
                );

        if (
            normalizedKey.includes(
                "strikeprice"
            ) ||
            normalizedKey ===
                "strikevalue"
        ) {
            const number =
                parseNumberFromText(
                    value
                );

            if (number !== null) {
                return number;
            }
        }
    }

    const metadata =
        getEventMetadata(
            instrument
        );

    const metadataKeys = [
        "strikePrice",
        "strike_price",
        "strike",
        "Strike Price",
        "STRIKE_PRICE",
        "strikeValue",
        "strike_value",
        "STRIKE_VALUE",
        "price",
        "Price"
    ];

    for (
        const key of metadataKeys
    ) {
        if (
            metadata[key] !==
                undefined &&
            metadata[key] !== null
        ) {
            const value =
                parseNumberFromText(
                    metadata[key]
                );

            if (value !== null) {
                return value;
            }
        }
    }

    for (
        const [key, value] of
        Object.entries(metadata)
    ) {
        const normalizedKey =
            String(key)
                .toLowerCase()
                .replace(
                    /[^a-z0-9]/g,
                    ""
                );

        if (
            normalizedKey.includes(
                "strikeprice"
            ) ||
            normalizedKey ===
                "strikevalue"
        ) {
            const number =
                parseNumberFromText(
                    value
                );

            if (number !== null) {
                return number;
            }
        }
    }

    const display =
        String(
            instrument.display_name ||
                ""
        );

    const displayMatches =
        display.match(
            /\$?\d+(?:,\d{3})*(?:\.\d+)?/g
        );

    if (
        displayMatches?.length
    ) {
        const numbers =
            displayMatches
                .map((value) =>
                    Number(
                        value
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
                )
                .filter(
                    (value) =>
                        value > 1000
                );

        if (numbers.length) {
            return Math.max(
                ...numbers
            );
        }
    }

    const symbol =
        String(
            instrument.symbol ||
                ""
        );

    const symbolMatches =
        symbol.match(
            /\d+(?:\.\d+)?/g
        );

    if (
        symbolMatches?.length
    ) {
        const numbers =
            symbolMatches
                .map((value) =>
                    Number(value)
                )
                .filter(
                    Number.isFinite
                )
                .filter(
                    (value) =>
                        value > 1000
                );

        if (numbers.length) {
            return Math.max(
                ...numbers
            );
        }
    }

    return null;
}

function normalizeInstrument(instrument) {
    const expiry =
        safeNumber(
            instrument.expiry_timestamp_ms
        );

    const attributes =
        getInstrumentAttributes(
            instrument
        );

    return {
        symbol: instrument.symbol,

        displayName:
            instrument.display_name,

        underlying:
            instrument.underlying_symbol,

        expiry,

        expiryISO:
            formatTimestamp(expiry),

        strikeIndex:
            getStrikeIndex(
                instrument
            ),

        strikeOperator:
            getStrikeOperator(
                instrument
            ),

        contractSize:
            safeNumber(
                instrument.contract_size
            ),

        priceTickSize:
            safeNumber(
                instrument.price_tick_size
            ),

        quantityTickSize:
            safeNumber(
                instrument.qty_tick_size
            ),

        strikePrice:
            extractStrikePrice(
                instrument
            ),

        tradable:
            instrument.tradable !== false,

        openTime:
            getOpenTime(
                instrument
            ),

        closeTime:
            getCloseTime(
                instrument
            ),

        periodCode:
            attributes.PERIOD_CODE ||
            attributes.period_code ||
            null,

        periodIndex:
            attributes.PERIOD_INDEX ||
            attributes.period_index ||
            null,

        displayPrecision:
            attributes.DISPLAY_PRECISION ||
            attributes.display_precision ||
            null,

        underlyingRoundingValue:
            attributes.UNDERLYING_ROUNDING_VALUE ||
            attributes.underlying_rounding_value ||
            null
    };
}

function selectCurrentContract(
    btcPrice
) {
    const currentTime =
        now();

    const candidates =
        instruments
            .map(normalizeInstrument)
            .filter(
                (instrument) =>
                    instrument.expiry &&
                    instrument.expiry >
                        currentTime &&
                    instrument.expiry -
                        currentTime <=
                        CONFIG.contractSelectionHorizonMs
            )
            .filter(
                (instrument) =>
                    instrument.strikePrice !==
                    null
            )
            .filter(
                (instrument) =>
                    instrument.tradable
            )
            .filter(
                (instrument) => {
                    if (
                        instrument.openTime &&
                        currentTime <
                            instrument.openTime
                    ) {
                        return false;
                    }

                    if (
                        instrument.closeTime &&
                        currentTime >
                            instrument.closeTime
                    ) {
                        return false;
                    }

                    return true;
                }
            );

    if (!candidates.length) {
        return null;
    }

    candidates.sort(
        (a, b) => {
            const aExpiryDistance =
                Math.abs(
                    a.expiry -
                        currentTime
                );

            const bExpiryDistance =
                Math.abs(
                    b.expiry -
                        currentTime
                );

            if (
                aExpiryDistance !==
                bExpiryDistance
            ) {
                return (
                    aExpiryDistance -
                    bExpiryDistance
                );
            }

            const aStrikeDistance =
                Math.abs(
                    a.strikePrice -
                        btcPrice
                );

            const bStrikeDistance =
                Math.abs(
                    b.strikePrice -
                        btcPrice
                );

            return (
                aStrikeDistance -
                bStrikeDistance
            );
        }
    );

    return candidates[0];
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
                }
            );

        const ticker =
            result?.data?.[0];

        if (!ticker) {
            return null;
        }

        return {
            bid: safeNumber(ticker.b),
            ask: safeNumber(ticker.k),
            last: safeNumber(ticker.a),
            bidSize: safeNumber(ticker.bs),
            askSize: safeNumber(ticker.ks),
            volume: safeNumber(ticker.v),
            timestamp: safeNumber(ticker.t)
        };
    } catch (exchangeError) {
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
                bid: safeNumber(ticker.b),
                ask: safeNumber(ticker.k),
                last: safeNumber(ticker.a),
                bidSize: safeNumber(ticker.bs),
                askSize: safeNumber(ticker.ks),
                volume: safeNumber(ticker.v),
                timestamp: safeNumber(ticker.t)
            };
        } catch (dcmError) {
            return null;
        }
    }
}

function updatePriceHistory(
    price,
    timestamp
) {
    if (
        price === null ||
        price === undefined
    ) {
        return;
    }

    priceHistory.push({
        price,
        timestamp
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
    for (const trade of trades) {
        const price =
            safeNumber(trade.p);

        const quantity =
            safeNumber(trade.q);

        const timestamp =
            safeNumber(trade.t);

        if (
            price === null ||
            quantity === null ||
            timestamp === null
        ) {
            continue;
        }

        const tradeId =
            String(
                trade.d ||
                    `${timestamp}-${price}-${quantity}`
            );

        const exists =
            tradeHistory.some(
                (item) =>
                    item.id ===
                    tradeId
            );

        if (exists) {
            continue;
        }

        tradeHistory.push({
            id: tradeId,
            price,
            quantity,
            side:
                String(
                    trade.s ||
                        ""
                ).toUpperCase(),
            timestamp
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

function calculateOrderBookMetrics(
    book
) {
    if (!book) {
        return null;
    }

    const bids =
        Array.isArray(book.bids)
            ? book.bids
            : [];

    const asks =
        Array.isArray(book.asks)
            ? book.asks
            : [];

    let weightedBidVolume = 0;
    let weightedAskVolume = 0;

    let bidVolume = 0;
    let askVolume = 0;

    const levels = Math.max(
        bids.length,
        asks.length
    );

    for (
        let i = 0;
        i < levels;
        i++
    ) {
        const weight =
            1 / (i + 1);

        const bid =
            bids[i];

        const ask =
            asks[i];

        const bidQty =
            Array.isArray(bid)
                ? safeNumber(bid[1])
                : safeNumber(
                      bid?.q
                  );

        const askQty =
            Array.isArray(ask)
                ? safeNumber(ask[1])
                : safeNumber(
                      ask?.q
                  );

        if (
            bidQty !== null
        ) {
            bidVolume += bidQty;

            weightedBidVolume +=
                bidQty * weight;
        }

        if (
            askQty !== null
        ) {
            askVolume += askQty;

            weightedAskVolume +=
                askQty * weight;
        }
    }

    const total =
        weightedBidVolume +
        weightedAskVolume;

    const imbalance =
        total > 0
            ? (
                  weightedBidVolume -
                  weightedAskVolume
              ) / total
            : 0;

    return {
        bidVolume,
        askVolume,
        weightedBidVolume,
        weightedAskVolume,
        imbalance
    };
}

function calculateTradeFlow() {
    const cutoff =
        now() -
        3 * 60 * 1000;

    const recent =
        tradeHistory.filter(
            (trade) =>
                trade.timestamp >=
                cutoff
        );

    let buyVolume = 0;
    let sellVolume = 0;

    for (const trade of recent) {
        if (
            trade.side ===
            "BUY"
        ) {
            buyVolume +=
                trade.quantity;
        } else if (
            trade.side ===
            "SELL"
        ) {
            sellVolume +=
                trade.quantity;
        }
    }

    const total =
        buyVolume +
        sellVolume;

    if (!total) {
        return {
            buyVolume: 0,
            sellVolume: 0,
            imbalance: 0
        };
    }

    return {
        buyVolume,
        sellVolume,
        imbalance:
            (
                buyVolume -
                sellVolume
            ) / total
    };
}

function priceAtOrBefore(
    timestamp
) {
    let result = null;

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
            timestamp
        ) {
            result =
                priceHistory[i]
                    .price;
            break;
        }
    }

    return result;
}

function calculateMomentum(
    currentPrice
) {
    const nowTime = now();

    const price1m =
        priceAtOrBefore(
            nowTime -
                60 * 1000
        );

    const price3m =
        priceAtOrBefore(
            nowTime -
                3 * 60 * 1000
        );

    const price5m =
        priceAtOrBefore(
            nowTime -
                5 * 60 * 1000
        );

    const momentum1m =
        price1m !== null
            ? currentPrice -
              price1m
            : null;

    const momentum3m =
        price3m !== null
            ? currentPrice -
              price3m
            : null;

    const momentum5m =
        price5m !== null
            ? currentPrice -
              price5m
            : null;

    return {
        momentum1m,
        momentum3m,
        momentum5m
    };
}

function calculateVolatility() {
    const nowTime = now();

    const oneMinute =
        priceHistory
            .filter(
                (item) =>
                    item.timestamp >=
                    nowTime -
                        60 * 1000
            )
            .map(
                (item) =>
                    item.price
            );

    const threeMinutes =
        priceHistory
            .filter(
                (item) =>
                    item.timestamp >=
                    nowTime -
                        3 * 60 * 1000
            )
            .map(
                (item) =>
                    item.price
            );

    return {
        volatility1m:
            standardDeviation(
                oneMinute
            ),

        volatility3m:
            standardDeviation(
                threeMinutes
            )
    };
}

function calculateVWAP() {
    const cutoff =
        now() -
        5 * 60 * 1000;

    const recent =
        tradeHistory.filter(
            (trade) =>
                trade.timestamp >=
                cutoff
        );

    if (!recent.length) {
        return null;
    }

    let totalValue = 0;
    let totalVolume = 0;

    for (const trade of recent) {
        totalValue +=
            trade.price *
            trade.quantity;

        totalVolume +=
            trade.quantity;
    }

    if (!totalVolume) {
        return null;
    }

    return (
        totalValue /
        totalVolume
    );
}

function calculateDistanceZScore(
    price,
    strike,
    volatility
) {
    if (
        price === null ||
        strike === null ||
        volatility === null ||
        volatility <= 0
    ) {
        return null;
    }

    return (
        (price - strike) /
        volatility
    );
}

function calculateDataQuality() {
    let score = 0;

    if (
        state.btcIndexPrice !==
        null
    ) {
        score += 25;
    }

    if (
        state.btcPrice !==
        null
    ) {
        score += 15;
    }

    if (
        priceHistory.length >=
        30
    ) {
        score += 20;
    }

    if (
        tradeHistory.length >=
        20
    ) {
        score += 15;
    }

    if (
        state.orderBookImbalance !==
        null
    ) {
        score += 15;
    }

    if (
        currentContract
    ) {
        score += 10;
    }

    return score;
}

function startRoundIfNeeded() {
    if (!currentContract) {
        return;
    }

    const expiry =
        currentContract.expiry;

    const roundId =
        createRoundId(expiry);

    if (
        currentRound?.id ===
        roundId
    ) {
        return;
    }

    currentRound = {
        id: roundId,

        symbol:
            currentContract.symbol,

        strike:
            currentContract.strikePrice,

        expiry,

        startedAt: now(),

        collectionStartPrice:
            state.btcPrice,

        forecastMade: false,

        forecast: null,

        forecastProbability:
            null,

        forecastConfidence:
            null,

        finalPrice: null,

        result: null
    };

    state.activeRoundId =
        roundId;

    state.collectionStartedAt =
        now();

    state.forecast =
        "COLLECTING";

    state.forecastProbability =
        null;

    state.forecastConfidence =
        null;
}

function secondsSinceRoundStart() {
    if (
        !currentRound
    ) {
        return 0;
    }

    return Math.max(
        0,
        Math.floor(
            (
                now() -
                currentRound.startedAt
            ) / 1000
        )
    );
}

function calculateForecast() {
    if (
        !currentContract ||
        state.btcPrice ===
            null ||
        state.strikePrice ===
            null
    ) {
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
            "COLLECTING";

        return;
    }

    if (
        state.secondsRemaining !==
            null &&
        state.secondsRemaining <=
            0
    ) {
        state.phase =
            "EXPIRED";

        return;
    }

    const price =
        state.btcPrice;

    const strike =
        state.strikePrice;

    const distance =
        price - strike;

    const volatility =
        state.volatility3m;

    const normalizedDistance =
        volatility &&
        volatility > 0
            ? distance /
              volatility
            : 0;

    const momentum1m =
        state.momentum1m ||
        0;

    const momentum3m =
        state.momentum3m ||
        0;

    const orderFlow =
        state.tradeFlow ||
        0;

    const bookPressure =
        state.orderBookImbalance ||
        0;

    let score = 0;

    score +=
        clamp(
            normalizedDistance,
            -3,
            3
        ) * 0.45;

    if (
        volatility &&
        volatility > 0
    ) {
        score +=
            clamp(
                momentum1m /
                    volatility,
                -3,
                3
            ) * 0.20;

        score +=
            clamp(
                momentum3m /
                    volatility,
                -3,
                3
            ) * 0.15;
    }

    score +=
        clamp(
            orderFlow,
            -1,
            1
        ) * 0.10;

    score +=
        clamp(
            bookPressure,
            -1,
            1
        ) * 0.10;

    const secondsRemaining =
        state.secondsRemaining ??
        900;

    const timeFactor =
        clamp(
            1 -
                secondsRemaining /
                    900,
            0,
            1
        );

    score *=
        0.75 +
        timeFactor * 0.25;

    const probability =
        1 /
        (
            1 +
            Math.exp(
                -score
            )
        );

    const confidence =
        Math.abs(
            probability - 0.5
        ) * 2;

    let forecast =
        "PASS";

    if (
        probability >=
        0.57
    ) {
        forecast =
            "YES";
    } else if (
        probability <=
        0.43
    ) {
        forecast =
            "NO";
    }

    state.forecast =
        forecast;

    state.forecastProbability =
        probability * 100;

    state.forecastConfidence =
        confidence * 100;

    state.modelScore =
        score;

    state.phase =
        "FORECASTING";

    if (
        currentRound &&
        !currentRound.forecastMade
    ) {
        currentRound.forecastMade =
            true;

        currentRound.forecast =
            forecast;

        currentRound.forecastProbability =
            probability * 100;

        currentRound.forecastConfidence =
            confidence * 100;

        currentRound.forecastTime =
            now();
    }
}

function calculateStateMetrics() {
    if (
        state.btcPrice ===
        null
    ) {
        return;
    }

    if (
        state.strikePrice !==
            null
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
    }

    const momentum =
        calculateMomentum(
            state.btcPrice
        );

    state.momentum1m =
        momentum.momentum1m;

    state.momentum3m =
        momentum.momentum3m;

    state.momentum5m =
        momentum.momentum5m;

    const volatility =
        calculateVolatility();

    state.volatility1m =
        volatility.volatility1m;

    state.volatility3m =
        volatility.volatility3m;

    const vwap =
        calculateVWAP();

    state.vwap =
        vwap;

    if (
        state.strikePrice !==
            null &&
        state.volatility3m !==
            null
    ) {
        state.distanceZScore =
            calculateDistanceZScore(
                state.btcPrice,
                state.strikePrice,
                state.volatility3m
            );
    }

    state.dataQuality =
        calculateDataQuality();

    if (
        currentRound
    ) {
        const elapsed =
            secondsSinceRoundStart();

        state.phase =
            elapsed <
            CONFIG.collectionSeconds
                ? "COLLECTING"
                : "FORECASTING";
    }
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

        const btcInstruments =
            loadedInstruments.filter(
                isBTCStrikeInstrument
            );

        console.log(
            `[ODIN] BTC Strike candidates after BTC/operator filter: ${btcInstruments.length}`
        );

        instruments =
            btcInstruments;

        state.connected = true;

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
            `[ODIN] BTC instruments with detected strikes: ${withStrikes.length}`
        );

        if (
            loadedInstruments.length > 0 &&
            btcInstruments.length === 0
        ) {
            const sample =
                loadedInstruments
                    .slice(0, 10)
                    .map(
                        (instrument) => ({
                            symbol:
                                instrument.symbol,

                            instType:
                                instrument.inst_type,

                            underlying:
                                instrument.underlying_symbol,

                            baseCcy:
                                instrument.base_ccy,

                            displayName:
                                instrument.display_name,

                            expiry:
                                instrument.expiry_timestamp_ms,

                            tradable:
                                instrument.tradable,

                            operator:
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
                "[ODIN] No BTC Strike instruments passed the filter. SAMPLE:",
                JSON.stringify(
                    sample,
                    null,
                    2
                )
            );
        }

        if (
            btcInstruments.length > 0 &&
            withStrikes.length === 0
        ) {
            const sample =
                btcInstruments
                    .slice(0, 10)
                    .map(
                        (instrument) => ({
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
                "[ODIN] BTC Strike instruments exist, but Odin could not detect their dollar strike prices. SAMPLE:",
                JSON.stringify(
                    sample,
                    null,
                    2
                )
            );
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

async function resolveCurrentContract() {
    if (
        state.btcPrice ===
        null
    ) {
        return;
    }

    const selected =
        selectCurrentContract(
            state.btcPrice
        );

    if (!selected) {
        if (
            instruments.length > 0 &&
            now() - lastNoContractLog >
                15000
        ) {
            lastNoContractLog =
                now();

            const normalized =
                instruments.map(
                    normalizeInstrument
                );

            const future =
                normalized.filter(
                    (instrument) =>
                        instrument.expiry &&
                        instrument.expiry >
                            now()
                );

            const withStrike =
                future.filter(
                    (instrument) =>
                        instrument.strikePrice !==
                        null
                );

            console.log(
                `[ODIN] No eligible contract | BTC instruments=${instruments.length} | future=${future.length} | futureWithStrike=${withStrike.length}`
            );

            if (
                withStrike.length ===
                0
            ) {
                console.log(
                    "[ODIN] No future BTC Strike instrument currently has a detected dollar strike."
                );
            }
        }

        currentContract =
            null;

        state.contractSymbol =
            null;

        state.strikePrice =
            null;

        state.contractExpiry =
            null;

        state.secondsRemaining =
            null;

        return;
    }

    if (
        currentContract?.symbol !==
        selected.symbol
    ) {
        currentContract =
            selected;

        console.log(
            `[ODIN] Active strike: ${selected.symbol} | Strike ${selected.strikePrice} | Operator ${selected.strikeOperator} | Expiry ${selected.expiryISO}`
        );

        startRoundIfNeeded();
    }

    state.contractSymbol =
        selected.symbol;

    state.strikePrice =
        selected.strikePrice;

    state.contractExpiry =
        selected.expiry;

    state.secondsRemaining =
        Math.max(
            0,
            Math.floor(
                (
                    selected.expiry -
                    now()
                ) / 1000
            )
        );
}

async function collectMarketData() {
    try {
        const [
            index,
            ticker,
            book,
            trades
        ] = await Promise.all([
            getBTCIndex(),
            getBTCPerpTicker(),
            getBTCBook(),
            getBTCTrades()
        ]);

        if (
            index?.price !== null
        ) {
            state.btcIndexPrice =
                index.price;
        }

        if (
            ticker?.last !== null
        ) {
            state.btcPrice =
                ticker.last;
        } else if (
            index?.price !== null
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
                timestamp: now(),
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
            ticker.bid !== null &&
            ticker.ask !== null
        ) {
            state.contractMid =
                (
                    ticker.bid +
                    ticker.ask
                ) / 2;

            state.marketProbability =
                clamp(
                    state.contractMid * 10,
                    0,
                    100
                );
        } else {
            state.contractMid =
                ticker.last;

            state.marketProbability =
                ticker.last !== null
                    ? clamp(
                          ticker.last * 10,
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

    completedRounds.push(
        {
            ...currentRound
        }
    );

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
        wins + losses;

    return {
        wins,
        losses,
        total,
        accuracy:
            total > 0
                ? (
                      wins /
                      total
                  ) * 100
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
            status: "online",
            service: "ODIN",
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