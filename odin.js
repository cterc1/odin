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
    instrumentRefreshMs: 60000,

    contractSelectionHorizonMs:
        14 *
        24 *
        60 *
        60 *
        1000,

    maxPriceHistory: 900,
    maxTradeHistory: 900,
    maxOrderBookHistory: 300,

    forecastHistoryLimit: 500,

    /*
     * PAPER FORECAST LOCK
     *
     * Odin must see the same direction repeatedly before
     * allowing a paper forecast to become locked.
     *
     * This is a stability safeguard for the paper model.
     * It is NOT a guarantee of prediction accuracy.
     */

    forecastStabilityRequired: 3,

    /*
     * Keep weak signals neutral.
     *
     * Odin will remain WAIT instead of forcing YES/NO when
     * the model is too close to the middle.
     */

    minimumForecastConfidence: 8,

    /*
     * Market/index integrity safeguards.
     */

    maxIndexAgeMs: 10000,

    maxIndexPerpDifferencePct: 1.5
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

    activeRoundId: null,

    /*
     * PAPER LOCK STATE
     */

    forecastLocked: false,
    lockedForecast: null,
    lockedProbability: null,
    lockedConfidence: null,
    lockedAt: null,
    lockedContractSymbol: null,
    lockedContractExpiry: null,

    /*
     * Data-integrity warning.
     *
     * This is deliberately not a buy/sell command.
     * It only indicates that Odin should not trust its
     * current paper forecast.
     */

    paperEmergency: false,
    paperEmergencyReason: null
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

let instrumentRefreshInProgress = false;

/*
 * Prevent multiple polls from running at the same time.
 *
 * Market collection and the DCM instrument refresh can take
 * longer than one second, so without this lock a new poll
 * could start before the previous one has finished.
 */

let pollInProgress = false;

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
     * Crypto.com's Strike Option display names can
     * expose the strike directly without a dollar sign.
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
            parsed !==
                null &&
            parsed >= 10000 &&
            parsed <= 1000000
        ) {
            return parsed;
        }
    }

    /*
     * Final fallback for Strike Option names that contain
     * a standalone BTC strike value.
     */

    const displayMatches =
        displayName.match(
            /\$?[0-9][0-9,]*(?:\.[0-9]+)?/g
        );

    if (
        displayMatches?.length
    ) {
        const numbers =
            displayMatches
                .map(
                    (value) =>
                        safeNumber(
                            value
                                .replace(
                                    /\$/g,
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
                        value >= 10000 &&
                        value <= 1000000
                );

        if (
            numbers.length
        ) {
            return Math.min(
                ...numbers
            );
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
        console.log(
            "[ODIN] Instrument refresh already in progress - skipping duplicate refresh"
        );

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

        console.log(
            `[ODIN] BTC Strike candidates after DCM metadata filter: ${btcInstruments.length}`
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
            btcInstruments;

        /*
         * IMPORTANT:
         *
         * If Odin is already collecting or forecasting
         * a paper round, keep that exact contract.
         *
         * BTC movement must NOT cause the round to jump
         * to another strike.
         */

        const lockedContractSymbol =
            currentRound?.symbol;

        const lockedContract =
            lockedContractSymbol
                ? instruments.find(
                      (instrument) =>
                          instrument.symbol ===
                          lockedContractSymbol
                  )
                : null;

        if (
            currentRound &&
            lockedContract
        ) {
            currentContract = {
                instrument:
                    lockedContract,

                expiry:
                    safeNumber(
                        lockedContract
                            .expiry_timestamp_ms
                    ),

                strike:
                    extractStrikePrice(
                        lockedContract
                    ),

                strikeIndex:
                    getStrikeIndex(
                        lockedContract
                    ),

                operator:
                    getStrikeOperator(
                        lockedContract
                    )
            };

            console.log(
                `[ODIN] Keeping locked paper contract: ${lockedContract.symbol}`
            );
        } else {
            currentContract =
                selectCurrentContract(
                    instruments
                );

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

function checkDataIntegrity() {
    const reasons = [];

    if (
        state.btcPrice === null
    ) {
        reasons.push(
            "BTC perp price unavailable"
        );
    }

    if (
        state.btcIndexPrice === null
    ) {
        reasons.push(
            "BTC index unavailable"
        );
    }

    if (
        state.lastUpdate === null
    ) {
        reasons.push(
            "market data has not updated"
        );
    } else if (
        now() -
            state.lastUpdate >
        CONFIG.maxIndexAgeMs
    ) {
        reasons.push(
            "market data is stale"
        );
    }

    /*
     * The index timestamp is checked separately.
     */

    if (
        state.btcIndexTimestamp !==
            undefined &&
        state.btcIndexTimestamp !==
            null
    ) {
        const indexAge =
            now() -
            state.btcIndexTimestamp;

        if (
            indexAge >
            CONFIG.maxIndexAgeMs
        ) {
            reasons.push(
                "BTC index timestamp is stale"
            );
        }
    }

    /*
     * This is only a data-integrity warning.
     * It does NOT tell the user to buy or sell.
     */

    if (
        state.btcIndexPrice !== null &&
        state.btcPrice !== null &&
        state.btcPrice !== 0
    ) {
        const differencePct =
            Math.abs(
                (
                    (
                        state.btcIndexPrice -
                        state.btcPrice
                    ) /
                    state.btcPrice
                ) *
                100
            );

        if (
            differencePct >
            CONFIG.maxIndexPerpDifferencePct
        ) {
            reasons.push(
                "BTC index/perpetual price divergence is unusually large"
            );
        }
    }

    if (
        state.dataQuality <
        70
    ) {
        reasons.push(
            "data quality is below the paper-model threshold"
        );
    }

    if (
        !priceHistory.length
    ) {
        reasons.push(
            "insufficient BTC price history"
        );
    }

    state.paperEmergency =
        reasons.length >
        0;

    state.paperEmergencyReason =
        reasons.length
            ? reasons.join(
                  "; "
              )
            : null;

    return (
        reasons.length ===
        0
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
            index &&
            index.price !==
                null
        ) {
            state.btcIndexPrice =
                index.price;

            state.btcIndexTimestamp =
                index.timestamp;
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
        ) / 1000
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

    if (
        state.btcPrice !==
            null &&
        state.strikePrice !==
            null
    ) {
        state.strikeDistance =
            state.btcPrice -
            state.strikePrice;

        state.strikeDistancePct =
            (
                (
                    state.btcPrice -
                    state.strikePrice
                ) /
                state.strikePrice
            ) *
            100;
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
            null
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

        forecastMade:
            false,

        /*
         * Lock bookkeeping.
         */

        forecastLocked:
            false,

        lockedForecast:
            null,

        lockedProbability:
            null,

        lockedConfidence:
            null,

        lockedAt:
            null,

        stabilityDirection:
            null,

        stabilityCount:
            0,

        lastCandidateProbability:
            null,

        result:
            null
    };

    state.activeRoundId =
        id;

    state.collectionStartedAt =
        now();

    state.forecastLocked =
        false;

    state.lockedForecast =
        null;

    state.lockedProbability =
        null;

    state.lockedConfidence =
        null;

    state.lockedAt =
        null;

    state.lockedContractSymbol =
        currentRound.symbol;

    state.lockedContractExpiry =
        currentRound.expiry;

    state.paperEmergency =
        false;

    state.paperEmergencyReason =
        null;

    state.phase =
        "COLLECTING";

    console.log(
        `[ODIN] Started paper round ${id}`
    );

    console.log(
        `[ODIN] Collecting BTC data for ${CONFIG.collectionSeconds} seconds before prediction`
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

        return;
    }

    startNewRound();

    if (
        !currentRound
    ) {
        return;
    }

    /*
     * Once the paper forecast is locked, NEVER recalculate
     * or flip its direction during the same contract.
     */

    if (
        currentRound.forecastLocked
    ) {
        state.phase =
            "LOCKED";

        state.forecast =
            currentRound.lockedForecast;

        state.forecastProbability =
            currentRound.lockedProbability;

        state.forecastConfidence =
            currentRound.lockedConfidence;

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

        return;
    }

    /*
     * Do not create a paper pick when data integrity is bad.
     */

    if (
        !checkDataIntegrity()
    ) {
        state.phase =
            "DATA_WARNING";

        state.forecast =
            "WAIT";

        state.forecastProbability =
            null;

        state.forecastConfidence =
            null;

        return;
    }

    if (
        state.btcPrice ===
            null ||
        state.strikePrice ===
            null
    ) {
        state.phase =
            "WAITING";

        state.forecast =
            "WAIT";

        console.log(
            "[ODIN] Forecast waiting: BTC price or strike price unavailable"
        );

        return;
    }

    state.phase =
        "FORECASTING";

    let score = 0;

    if (
        state.strikeDistancePct !==
        null
    ) {
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
        score += clamp(
            state.acceleration *
                2,
            -5,
            5
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

    const confidence =
        Math.abs(
            probability -
                50
        );

    state.forecastProbability =
        probability;

    state.forecastConfidence =
        confidence;

    /*
     * Neutral zone.
     *
     * Odin refuses to force a direction when the signal
     * is not strong enough.
     */

    if (
        confidence <
        CONFIG.minimumForecastConfidence
    ) {
        currentRound.stabilityDirection =
            null;

        currentRound.stabilityCount =
            0;

        currentRound.lastCandidateProbability =
            probability;

        state.forecast =
            "WAIT";

        state.phase =
            "FORECASTING";

        console.log(
            `[ODIN] Paper forecast remains WAIT | Confidence ${confidence.toFixed(2)}% is below stability threshold`
        );

        return;
    }

    const candidate =
        probability >=
        50
            ? "YES"
            : "NO";

    /*
     * Stability counter.
     *
     * The same candidate must appear repeatedly.
     * If the model changes sides, the counter resets.
     */

    if (
        currentRound.stabilityDirection ===
        candidate
    ) {
        currentRound.stabilityCount +=
            1;
    } else {
        currentRound.stabilityDirection =
            candidate;

        currentRound.stabilityCount =
            1;
    }

    currentRound.lastCandidateProbability =
        probability;

    state.forecast =
        "WAIT";

    /*
     * The direction is not locked until it survives
     * the required number of consecutive calculations.
     */

    if (
        currentRound.stabilityCount <
        CONFIG.forecastStabilityRequired
    ) {
        state.phase =
            "FORECASTING";

        console.log(
            `[ODIN] Candidate ${candidate} | Stability ${currentRound.stabilityCount}/${CONFIG.forecastStabilityRequired} | Probability: ${probability.toFixed(2)}%`
        );

        return;
    }

    /*
     * LOCK THE PAPER FORECAST.
     *
     * From this point forward the direction belongs to
     * this exact contract and cannot flip simply because
     * BTC moves.
     */

    currentRound.forecast =
        candidate;

    currentRound.forecastProbability =
        probability;

    currentRound.confidence =
        confidence;

    currentRound.forecastMade =
        true;

    currentRound.forecastLocked =
        true;

    currentRound.lockedForecast =
        candidate;

    currentRound.lockedProbability =
        probability;

    currentRound.lockedConfidence =
        confidence;

    currentRound.lockedAt =
        now();

    state.forecast =
        candidate;

    state.forecastProbability =
        probability;

    state.forecastConfidence =
        confidence;

    state.forecastLocked =
        true;

    state.lockedForecast =
        candidate;

    state.lockedProbability =
        probability;

    state.lockedConfidence =
        confidence;

    state.lockedAt =
        now();

    state.lockedContractSymbol =
        currentRound.symbol;

    state.lockedContractExpiry =
        currentRound.expiry;

    state.phase =
        "LOCKED";

    console.log(
        `[ODIN] PAPER FORECAST LOCKED | ${candidate} | Probability: ${probability.toFixed(2)}% | Confidence: ${confidence.toFixed(2)}% | Contract: ${currentRound.symbol} | Stability: ${currentRound.stabilityCount}/${CONFIG.forecastStabilityRequired}`
    );
}

function resolveCurrentContract() {
    if (
        !instruments.length
    ) {
        currentContract =
            null;

        return;
    }

    /*
     * LOCKED CONTRACT SYSTEM
     *
     * Once a paper round exists, Odin must continue using
     * that exact instrument until the round expires.
     *
     * BTC movement cannot cause a new strike to be selected.
     */

    if (
        currentRound &&
        currentRound.symbol
    ) {
        const lockedInstrument =
            instruments.find(
                (instrument) =>
                    instrument.symbol ===
                    currentRound.symbol
            );

        if (
            lockedInstrument
        ) {
            currentContract = {
                instrument:
                    lockedInstrument,

                expiry:
                    safeNumber(
                        lockedInstrument
                            .expiry_timestamp_ms
                    ),

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

            state.contractSymbol =
                lockedInstrument.symbol ||
                null;

            state.contractExpiry =
                safeNumber(
                    lockedInstrument
                        .expiry_timestamp_ms
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

            state.activeRoundId =
                createRoundId(
                    state.contractExpiry
                );

            state.lockedContractSymbol =
                currentRound.symbol;

            state.lockedContractExpiry =
                currentRound.expiry;

            return;
        }
    }

    /*
     * No active round exists.
     *
     * This is the ONLY normal point where Odin chooses a
     * fresh contract.
     */

    const selected =
        selectCurrentContract(
            instruments
        );

    if (
        !selected
    ) {
        currentContract =
            null;

        return;
    }

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

    state.activeRoundId =
        createRoundId(
            state.contractExpiry
        );

    console.log(
        `[ODIN] Fresh paper contract selected: ${instrument.symbol}`
    );
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
        `[ODIN] Round ${currentRound.id} resolved: ${result} | Final Index: ${finalPrice} | Strike: ${currentRound.strike}`
    );

    currentRound =
        null;

    currentContract =
        null;

    state.forecast =
        "WAIT";

    state.forecastProbability =
        null;

    state.forecastConfidence =
        null;

    state.forecastLocked =
        false;

    state.lockedForecast =
        null;

    state.lockedProbability =
        null;

    state.lockedConfidence =
        null;

    state.lockedAt =
        null;

    state.lockedContractSymbol =
        null;

    state.lockedContractExpiry =
        null;

    state.activeRoundId =
        null;

    state.phase =
        "WAITING";
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

        lockedAtISO:
            formatTimestamp(
                state.lockedAt
            ),

        lockedContractExpiryISO:
            formatTimestamp(
                state.lockedContractExpiry
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
            if (
                !instrumentRefreshInProgress
            ) {
                lastInstrumentRefresh =
                    currentTime;

                await refreshInstruments();
            }
        }

        await collectMarketData();

        resolveCurrentContract();

        await collectContractData();

        calculateStateMetrics();

        calculateForecast();

        evaluateExpiredRound();

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
            "Forecast lock: 3 consecutive signals"
        );

        console.log(
            "=========================================="
        );

        console.log("");

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