#region Using declarations
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.IO;
using System.Linq;
using System.Text;
using System.Windows.Media;
using NinjaTrader.Cbi;
using NinjaTrader.Data;
using NinjaTrader.Gui.Tools;
using NinjaTrader.NinjaScript;
using NinjaTrader.NinjaScript.DrawingTools;
using NinjaTrader.NinjaScript.Strategies;
#endregion

// ============================================================================
//  >>> MODIFIED BUILD — ALL LICENSE / ACTIVATION CODE REMOVED <<<
//
//  This copy contains NO license checks of any kind:
//    - no License Key / License Product parameters
//    - no KeyAuth / Supabase server validation
//    - no HWID / machine-ID binding, no tier or expiry gating
//    - no hourly re-validation, no transient-grace logic
//    - no license message boxes, no activation banner
//
//  The rule set is selected directly by the "Edition" parameter
//  (Standard / Enhanced / Elite / Ultimate / Paragon). Default = Ultimate.
//  All trading logic is untouched.
// ============================================================================

// ============================================================================
//  OCTVERSION2 — GhostAlgo v1.3.0 (all tiers) + Paragon, on ONE 1-TICK series.
//
//  NO CHART TIMEFRAME TO PICK. Run it on NQ (or MNQ) "Tick / 1" — from a chart,
//  the Strategies tab, or the Strategy Analyzer. The 15-minute / 60-minute signal
//  bars are built INSIDE the strategy from the tick stream on clock boundaries,
//  so they line up with a normal 15-min / 60-min chart on the CME US Index
//  Futures template. Stops / targets are NinjaTrader's own managed orders on the
//  tick series, so a backtest fills them tick by tick (no OHLC guessing).
//
//  NO LICENSE / NO KEY. The Edition parameter picks the rule set:
//  Standard, Enhanced, Elite, Ultimate or Paragon.
//
//    Mode           Signal bars   SL / TP        Exit
//    ─────────────  ───────────   ───────────    ─────────────────────────────
//    Standard       15-min        3 / 15         stop + target
//    Standard-Alt   60-min        8 / ladder     point ladder (Standard key + toggle)
//    Enhanced       60-min        10 / 30        stop + target
//    Elite          60-min        3 / 18         stop + target
//    Ultimate       60-min        10 / ladder    point ladder
//    Paragon        60-min        10 / 24        stop + target
//
//  EVERY v1.3.0 BEHAVIOUR KEPT: signal rules + walk-forward quantiles byte for
//  byte, daily freeze 14:55–17:15 CT (+ session-end branch, pending-entry
//  cancel, nuclear backstop), news filter, front-run (lock/fire before the
//  internal bar's close), stop-limit exit + fallback, point ladder, MNQ bridge
//  (signals from NQ ticks, execution on MNQ), history-adequacy gate,
//  rejection handler + circuit breaker, latency logging. Paragon keeps its own
//  rules exactly: no freeze, no news. (The hourly license re-check that used to
//  sit here has been removed with the rest of the licensing code.)
//
//  DROPPED (dead in v1.3.0): trail / path-efficiency / trend filters — every
//  tier had them switched off. Chart-period + bar-alignment gates are replaced
//  by one check: the data series must be 1 Tick.
//
//  Times are the chart/PC clock, which must be US Central (same as v1.3.0).
// ============================================================================

namespace NinjaTrader.NinjaScript.Strategies
{
    public class OCTVERSION2 : Strategy
    {
        public enum AlgoEdition { Standard, Enhanced, Elite, Ultimate, Paragon }

        // ━━━ LOCKED PARAMS (v1.3.0) ━━━
        private const string STRATEGY_VERSION    = "2.1.0-oct2";
        private const string TAG_PREFIX          = "ghost_";
        private const int    WARMUP_BARS         = 1000;
        private const int    BARS_REQUIRED       = 1000;   // = v1.3.0 BarsRequiredToTrade on the signal chart
        private const double QUANTILE_LEVEL      = 0.80;
        private const int    BIG_DELTA_TICK      = 20;
        private const double BODYSIZE_ALT_CUTOFF = 47.25;
        private const double IMBALANCE_RATIO     = 5.0;
        private const int    POC_CONT_DOWN_BARS  = 3;
        private const bool   ENABLE_BIDIR        = true;
        private const int    PANEL_REFRESH_N     = 5;
        private static readonly DateTime MIN_REQUIRED_HISTORY = new DateTime(2025, 1, 1);

        // ━━━ PARAGON (locked, = Selling\@@Paragon.cs) ━━━
        private const double PAR_SL       = 10.0;
        private const double PAR_TP       = 24.0;
        private const int    PAR_WARMUP   = 1000;
        private const double PAR_QUANTILE = 0.90;
        private const bool   PAR_BIDIR    = true;

        private enum Mode { None, Standard, Enhanced, Elite, Ultimate, Paragon }

        // ─── Run state ──────────────────────────────────────────────────────
        private bool   _armed;
        private Mode   _mode = Mode.None;
        private string _failureReason = "";

        // ─── Series state ───────────────────────────────────────────────────
        private bool   _tfOk;                 // primary series is 1 Tick
        private bool   _tfWarned, _tfMessageBoxShown;
        private string _currentTfLabel = "(unknown)";
        private bool   _isMicroMode;          // MNQ primary → signals from an added NQ tick series
        private string _nqContractSym = "";
        private int    _signalBip;            // 0 (NQ) or 1 (NQ ticks under an MNQ primary)
        private bool   _bridgeViable = true;
        private bool   _initDone;

        // ─── Internal signal bar ────────────────────────────────────────────
        private int    _periodMin = 60;
        private long   _curBucket = -1;
        private double _bOpen, _bClose;
        private double _bHigh, _bLow;            // true extremes of the forming internal bar

        // ─── STANDARD (noise-band intraday momentum) ──────────────────────────
        //
        // Built on the internal 1-minute bars so it lives on the one 1-tick
        // series like every other mode here.
        //
        // TIMEZONE: the session is Eastern by convention. This file already
        // mandates a US Central PC clock (the 14:55-17:15 freeze is stated in CT),
        // so the session is expressed in CENTRAL and there is exactly one clock
        // convention in the file. 09:30 ET = 08:30 CT, 16:00 ET = 15:00 CT.
        // Both zones shift together on US DST, so the mapping holds year round.
        private static readonly TimeSpan SN_RTH_OPEN   = new TimeSpan( 8, 30, 0); // 09:30 ET
        private static readonly TimeSpan SN_RTH_CLOSE  = new TimeSpan(15,  0, 0); // 16:00 ET
        private static readonly TimeSpan SN_LAST_ENTRY = new TimeSpan(14, 30, 0); // 15:30 ET
        private static readonly TimeSpan SN_FLATTEN    = new TimeSpan(14, 58, 0); // 15:58 ET

        private const int    SN_LOOKBACK_DAYS    = 14;    // sessions of sigma history
        private const double SN_BAND_MULT        = 1.0;
        private const int    SN_CHECK_MINUTES    = 30;    // entries only on the half hour
        private const int    SN_MAX_TRADES_DAY   = 5;
        private const double SN_BRACKET_ATR      = 0.16;  // stop = 0.16 x avg daily range
        private const double SN_REWARD_RISK      = 2.0;
        private const double SN_MIN_STOP_POINTS  = 4.0;

        private long     _snBarVolume;                    // volume of the forming internal bar
        private DateTime _snDate = DateTime.MinValue;     // RTH date currently open
        private double   _snRthOpen;                      // first RTH price today
        private double   _snPrevRthClose = double.NaN;    // yesterday's RTH close
        private double   _snLastRthClose = double.NaN;    // most recent RTH close seen
        private double   _snDayHigh, _snDayLow;
        private double   _snSumPV, _snSumV;               // session VWAP accumulators
        private int      _snTradesToday;
        private bool     _snSessionOpen;

        // sigma(m): mean over the last SN_LOOKBACK_DAYS sessions of
        // |close at minute m / RTH open - 1|. Keyed by minute offset from the open.
        private readonly Dictionary<int, List<double>> _snSigmaHist = new Dictionary<int, List<double>>();
        private readonly Dictionary<int, double>       _snTodayDev  = new Dictionary<int, double>();
        private readonly List<double>                  _snDayRanges = new List<double>();
        private bool   _firstBarPartial = true;
        private int    _barsBuilt;

        // ─── History adequacy (v1.3.0) ──────────────────────────────────────
        private bool     _historyAdequate = true;
        private bool     _firstTradeRecorded;
        private bool     _firstTradeCheckDone;
        private DateTime _firstTradeTime = DateTime.MaxValue;
        private bool     _historyMessageBoxShown;
        private int      _historyDormantLogCount;

        // ─── DATA INTEGRITY PREFLIGHT ───────────────────────────────────────
        //  Why this exists: the signal set is reconstructed from the customer's
        //  own tick import, and every customer builds that differently. A client
        //  running NON-BACK-ADJUSTED per-contract data gets a price series that
        //  steps by the roll spread every quarter. Measured against a known-good
        //  run that produced a price offset of -1,510 pts in 2025Q2 decaying to
        //  exactly 0.00 in the front month, and only 36% of signal bars in common.
        //  The strategy used to run on that silently and the customer reported it
        //  as an algorithm fault. Now it checks and says so.
        //  NOTE ON THRESHOLDS: a magnitude test alone cannot separate a contract
        //  roll from a Sunday-open gap. Measured on a known-good back-adjusted
        //  archive (14,682 bars), legitimate session-open gaps reach 404.50 pts,
        //  while the offending client's roll steps were 257-491 pts. They overlap.
        //  So gaps are reported for information ONLY and never raise the warning.
        //  The FINGERPRINT is what decides, because it is exact: any difference in
        //  the reference window changes the hash.
        private const double ROLL_GAP_PTS = 250.0;   // informational reporting only
        private const int    FP_YEAR = 2026, FP_MONTH = 1;  // fixed fingerprint window
        //  Set this to the value this build prints on a known-good data set, then
        //  re-export. Left empty, the strategy prints its hash and judges nothing.
        private const string EXPECTED_FP = "";
        private bool     _dataMessageBoxShown;
        private double   _prevSigClose;
        private int      _gapCount;
        private double   _worstGap;
        private int      _gapsInRollMonths;
        private string   _gapList = "";
        private ulong    _fpHash  = 14695981039346656037UL;   // FNV-1a offset basis
        private int      _fpBars;
        private DateTime _firstBarTime = DateTime.MaxValue;   // fallback when no trade ever fires

        private double _slPts, _tpPts;
        private string _entryLongTag  = "GhostL";
        private string _entryShortTag = "GhostS";

        // ─── Per-bar tick aggregation ───────────────────────────────────────
        private Dictionary<double, long> askVol;
        private Dictionary<double, long> bidVol;
        private double lastPrice;
        private int    barBigDeltaCount;
        private long   cumDelta, cumDeltaMax, cumDeltaMin;

        // ─── POC tracking (Enhanced) ────────────────────────────────────────
        private double prevPOC;
        private bool   prevPOCValid;
        private int    contDownCount;

        // ─── Walk-forward quantile trackers ─────────────────────────────────
        private SortedList<double, int> bdcFreq, dmFreq, bsicFreq, bodySizeFreq;
        private int                     bdcTotal, dmTotal, bsicTotal, bodySizeTotal;

        // ─── Counters ───────────────────────────────────────────────────────
        private int  barsProcessed;
        private long totalTicks;
        private int  signalsFiredLong, signalsFiredShort;
        private int  qualifyingBarsLong, qualifyingBarsShort;
        private int  _frozenBars, _newsBars;

        // ─── Front-run ──────────────────────────────────────────────────────
        private readonly object _entryLock = new object();
        private volatile bool   _frDecisionReady;
        private bool            _frDecisionShouldTrade;
        private int             _frDecisionDir;
        private bool            _frLocked, _frEntered;
        private DateTime        _frBarOpenTime = DateTime.MinValue;
        private double          _frBarOpen;

        // ─── Stop-limit exit ────────────────────────────────────────────────
        private bool   _sleExitPlaced;
        private double _sleStopPrice;
        private bool   _sleLong;

        // ─── Entry bookkeeping ──────────────────────────────────────────────
        private bool   _inLong, _inShort;
        private double _entryPrice;

        // ─── Point ladder (v1.3.0) ──────────────────────────────────────────
        private const double UL_LADDER_ARM = 15.0, UL_LADDER_RUNG = 15.0, UL_LADDER_LOCK = 10.0;
        private bool   _useLadder;
        private double _ladArm, _ladRung, _ladLock;
        private bool   _ladActive;
        private int    _ladDir;
        private double _ladEntryPx, _ladPeakPts, _ladStopPx;
        private int    _ladRungsSet;

        // ─── Daily freeze (v1.3.0) ──────────────────────────────────────────
        private const int FREEZE_PRECLOSE_MIN = 65;    // SessionEnd - 65 min = 14:55 CT
        private const int FREEZE_POSTEND_MIN  = 75;    // SessionEnd + 75 min = 17:15 CT
        private const int FREEZE_CT_START_MIN = 895;   // 14:55
        private const int FREEZE_CT_END_MIN   = 1035;  // 17:15
        private const string FREEZE_OVERLAY_TAG = "ghost_freeze_overlay";
        private SessionIterator _closeGuardSessionIter;
        private bool     _freezeActive;
        private int      _freezeBlocksLoggedToday;
        private DateTime _freezeBlocksLogResetDay = DateTime.MinValue;
        private DateTime _freezeDiagPrintedForDay = DateTime.MinValue;

        // ─── Latency logging ────────────────────────────────────────────────
        private Dictionary<string, DateTime> _signalTimeByEntryTag  = new Dictionary<string, DateTime>();
        private Dictionary<string, double>   _signalPriceByEntryTag = new Dictionary<string, double>();

        // ─── Rejection handler ──────────────────────────────────────────────
        private int  _rejectionFlattenCooldownUntilTick;
        private int  _rejectionBurstWindowStartTick;
        private int  _rejectionBurstCount;
        private int  _circuitBreakerUntilTick;
        private bool _circuitBreakerAnnounced;
        private const int FLATTEN_COOLDOWN_MS = 2000;
        private const int BURST_WINDOW_MS     = 5000;
        private const int BURST_THRESHOLD     = 5;
        private const int CIRCUIT_BREAK_MS    = 30000;

        // Position on the EXECUTION instrument. Plain `Position` follows BarsInProgress,
        // which is the NQ signal series under the MNQ bridge.
        private Position ExecPos { get { return Positions[0]; } }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  ON STATE CHANGE
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Description = "OCTVERSION2 — Standard / Enhanced / Elite / Ultimate / Paragon rule sets "
                            + "on a single 1-tick series. The Edition parameter picks the rule set.";
                Name        = "OCTVERSION2";
                Calculate   = Calculate.OnBarClose;          // on a 1-tick series = every tick
                EntriesPerDirection = 1;
                EntryHandling       = EntryHandling.AllEntries;
                IsExitOnSessionCloseStrategy = false;
                IsInstantiatedOnEachOptimizationIteration = true;
                IncludeCommission   = true;
                PrintTo             = PrintTo.OutputTab2;
                BarsRequiredToTrade = 1;                     // warmup is counted in internal bars instead
                RealtimeErrorHandling = RealtimeErrorHandling.IgnoreAllErrors;

                Edition              = AlgoEdition.Ultimate;
                Quantity             = 1;
                BypassTickDataCheck  = false;
                LogExecutionLatency  = false;

                FrontRunEnabled      = false;
                LockBeforeMs         = 3000;
                EnterBeforeMs        = 600;
                FrontRunLogs         = false;
                UseStopLimitExit     = false;
                StopLimitFallbackPts = 0.25;
                SkipNews       = true;
                NewsWindowMins = 1;
                NewsTime1      = 730;
                NewsTime2      = 1300;
                NewsTime3      = 1600;
                NewsTime4      = 0;
                NewsTime5      = 0;
            }
            else if (State == State.Configure)
            {
                // 1. Edition → mode. No license gate: it always runs.
                _mode  = ModeFromEdition(Edition);
                _armed = true;
                SetModeParams();

                // 2. Series check — the ONLY timeframe rule: primary must be 1 Tick.
                _tfOk = false;
                try
                {
                    var bp = BarsPeriod;
                    _currentTfLabel = bp == null ? "(unknown)" : (bp.Value + " " + bp.BarsPeriodType);
                    _tfOk = bp != null && bp.BarsPeriodType == BarsPeriodType.Tick && bp.Value == 1;
                }
                catch { _tfOk = false; _currentTfLabel = "(error reading data series)"; }

                // 3. MNQ bridge — signals from NQ ticks, execution + ladder on the MNQ ticks.
                _isMicroMode = false; _signalBip = 0; _nqContractSym = "";
                try
                {
                    if (Instrument != null && Instrument.MasterInstrument != null
                        && string.Equals(Instrument.MasterInstrument.Name, "MNQ", StringComparison.OrdinalIgnoreCase))
                    {
                        _isMicroMode = true;
                        DateTime exp = Instrument.Expiry;
                        _nqContractSym = "NQ " + (exp == DateTime.MinValue ? DateTime.Now.ToString("MM-yy") : exp.ToString("MM-yy"));
                    }
                }
                catch { _isMicroMode = false; }

                if (_armed && _tfOk && _isMicroMode)
                {
                    try { AddDataSeries(_nqContractSym, BarsPeriodType.Tick, 1); } catch { }
                    _signalBip = 1;
                }

                // 4. Brackets.
                if (_mode != Mode.None && !UseStopLimitExit) SetupBrackets();
            }
            else if (State == State.DataLoaded)
            {
                if (Quantity < 1)   Quantity = 1;
                if (Quantity > 100) Quantity = 100;

                _bridgeViable = true;
                if (_isMicroMode && _armed && _tfOk)
                {
                    bool nqTickOk = BarsArray.Length > 1 && BarsArray[1] != null && BarsArray[1].Count > 0;
                    if (!nqTickOk)
                    {
                        _bridgeViable  = false;
                        _armed         = false;
                        _failureReason = "MNQ requires NQ tick data. Load " + _nqContractSym
                                       + " tick history (Tools → Historical Data), or run on NQ instead.";
                        Print("[OCTVERSION2] ⚠ MNQ BRIDGE UNAVAILABLE — " + _failureReason);
                    }
                }

                try { _closeGuardSessionIter = new SessionIterator(BarsArray[0]); } catch { _closeGuardSessionIter = null; }

                InitRuntimeState();
                _initDone = true;
                LogStartupBanner();
                PaintAllChrome();

                if (_armed && !_tfOk && !_tfMessageBoxShown)
                {
                    _tfMessageBoxShown = true;
                    ShowTfMismatchMessageBox();
                }
            }
            else if (State == State.Realtime)
            {
                if (!_firstTradeCheckDone) EvaluateFirstTrade();   // runs even with zero trades — bad data must still report
            }
            else if (State == State.Terminated)
            {
                if (!_initDone) return;
                if (!_firstTradeCheckDone) EvaluateFirstTrade();   // runs even with zero trades — bad data must still report
                LogTerminationSummary();
            }
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  MODE PARAMS + BRACKETS
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private static Mode ModeFromEdition(AlgoEdition edition)
        {
            switch (edition)
            {
                case AlgoEdition.Standard: return Mode.Standard;
                case AlgoEdition.Enhanced: return Mode.Enhanced;
                case AlgoEdition.Elite:    return Mode.Elite;
                case AlgoEdition.Ultimate: return Mode.Ultimate;
                case AlgoEdition.Paragon:  return Mode.Paragon;
                default:                   return Mode.Ultimate;
            }
        }

        private void SetModeParams()
        {
            _useLadder = false; _ladArm = _ladRung = _ladLock = 0;
            _periodMin = 60;
            switch (_mode)
            {
                // ── TIER SWAP (v2.0) ──────────────────────────────────────────
                //  STANDARD now runs the DELTA/POC engine  (was Enhanced)
                //  ENHANCED now runs the NOISE-BAND engine (was Standard)
                //  The engines are unchanged; only which tier serves them moved.
                //  Entry tags stay with the TIER so client logs read correctly.
                case Mode.Standard:
                    // Delta/POC edge: 1-hour bars, fixed 10/30 bracket.
                    _slPts = 10.0; _tpPts = 30.0; _periodMin = 60;
                    _entryLongTag = "StdL"; _entryShortTag = "StdS";
                    break;
                case Mode.Enhanced:
                    // Noise-band edge: 1-minute bars, volatility-scaled bracket
                    // recomputed per entry in BarLogic_NoiseBand. These are only the
                    // fallback values used before the first bracket is calculated.
                    _slPts = SN_MIN_STOP_POINTS; _tpPts = SN_MIN_STOP_POINTS * SN_REWARD_RISK; _periodMin = 1;
                    _entryLongTag = "EnhL"; _entryShortTag = "EnhS";
                    break;
                case Mode.Elite:
                    _slPts = 3.0;  _tpPts = 18.0;
                    _entryLongTag = "EliteL"; _entryShortTag = "EliteS";
                    break;
                case Mode.Ultimate:
                    _slPts = 10.0; _tpPts = 30.0;
                    _entryLongTag = "UltL"; _entryShortTag = "UltS";
                    _useLadder = true; _ladArm = UL_LADDER_ARM; _ladRung = UL_LADDER_RUNG; _ladLock = UL_LADDER_LOCK;
                    break;
                case Mode.Paragon:
                    _slPts = PAR_SL; _tpPts = PAR_TP;
                    _entryLongTag = "ParagonL"; _entryShortTag = "ParagonS";
                    break;
            }
            // Stop-limit mode runs its own exits; the managed ladder must stand down.
            if (UseStopLimitExit) _useLadder = false;
        }

        private string ModeName()
        {
            switch (_mode)
            {
                case Mode.Standard:    return "STANDARD";
                case Mode.Enhanced:    return "ENHANCED";
                case Mode.Elite:       return "ELITE";
                case Mode.Ultimate:    return "ULTIMATE";
                case Mode.Paragon:     return "PARAGON";
                default:               return "—";
            }
        }

        private void SetupBrackets()
        {
            int slTicks = (int)Math.Round(_slPts * 4);   // NQ / MNQ tick = 0.25
            int tpTicks = (int)Math.Round(_tpPts * 4);
            try
            {
                SetStopLoss(_entryLongTag,  CalculationMode.Ticks, slTicks, false);
                SetStopLoss(_entryShortTag, CalculationMode.Ticks, slTicks, false);
                // Ladder modes run with NO profit target (NT cannot un-assign one).
                if (!_useLadder)
                {
                    SetProfitTarget(_entryLongTag,  CalculationMode.Ticks, tpTicks);
                    SetProfitTarget(_entryShortTag, CalculationMode.Ticks, tpTicks);
                }
            }
            catch { }
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  POINT LADDER (v1.3.0) — ratchets on every EXECUTION tick
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private double SnapExec(double px)
        {
            try
            {
                double ts = BarsArray[0].Instrument.MasterInstrument.TickSize;
                if (ts > 0) return Math.Round(px / ts) * ts;
            }
            catch { }
            return Math.Round(px * 4.0) / 4.0;
        }

        private void LadderOnEntryFill(double price, bool isLong)
        {
            if (!_useLadder) return;
            _ladActive   = true;
            _ladDir      = isLong ? 1 : -1;
            _ladEntryPx  = price;
            _ladPeakPts  = 0;
            _ladRungsSet = 0;
            _ladStopPx   = SnapExec(price - _ladDir * _slPts);
            Print("[GHOST] LADDER armed " + (isLong ? "LONG " : "SHORT") + " entry=" + price.ToString("F2")
                  + "  stop=" + _ladStopPx.ToString("F2") + "  (-" + _slPts.ToString("F0") + " pts)");
        }

        private void LadderReset()
        {
            _ladActive = false; _ladDir = 0; _ladPeakPts = 0; _ladRungsSet = 0; _ladStopPx = 0;
            if (!_useLadder) return;
            int slTicks = (int)Math.Round(_slPts * 4);
            try
            {
                SetStopLoss(_entryLongTag,  CalculationMode.Ticks, slTicks, false);
                SetStopLoss(_entryShortTag, CalculationMode.Ticks, slTicks, false);
            }
            catch { }
        }

        private void LadderUpdate(double px)
        {
            if (!_useLadder || !_ladActive) return;
            try
            {
                if (ExecPos.MarketPosition == MarketPosition.Flat) { LadderReset(); return; }

                double anchor = ExecPos.AveragePrice > 0 ? ExecPos.AveragePrice : _ladEntryPx;
                if (anchor <= 0) return;

                double pts = _ladDir * (px - anchor);
                if (pts <= _ladPeakPts) return;
                _ladPeakPts = pts;
                if (_ladPeakPts < _ladArm) return;

                int rung = 1 + (int)Math.Floor((_ladPeakPts - _ladArm) / _ladRung);
                if (rung <= _ladRungsSet) return;

                double lockPts = _ladArm + (rung - 1) * _ladRung - _ladLock;
                double newStop = SnapExec(anchor + _ladDir * lockPts);
                if (_ladDir > 0 && newStop <= _ladStopPx) return;
                if (_ladDir < 0 && newStop >= _ladStopPx) return;

                _ladRungsSet = rung;
                _ladStopPx   = newStop;
                SetStopLoss(_ladDir > 0 ? _entryLongTag : _entryShortTag, CalculationMode.Price, _ladStopPx, false);

                Print("[GHOST] LADDER rung " + rung + "  peak=+" + _ladPeakPts.ToString("F2")
                      + "  stop -> " + _ladStopPx.ToString("F2") + "  (locked +" + lockPts.ToString("F0") + " pts)");
            }
            catch { }
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  HISTORY ADEQUACY (v1.3.0) — Standard / Elite / Ultimate only
        //  Follows the v2.0 tier swap: the engines needing a deep warmup are the
        //  quantile ones. STANDARD (delta/POC) and ULTIMATE build a footprint and
        //  a 1000-bar expanding quantile; ELITE needs the same bar count for its
        //  BodySize quantile. ENHANCED now runs the noise band, which only needs
        //  14 sessions of sigma history and is excluded.
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private bool HistoryCheckApplies()
        {
            return _mode == Mode.Standard || _mode == Mode.Elite || _mode == Mode.Ultimate;
        }

        private bool HistoryBlocksEntries()
        {
            return !_historyAdequate && HistoryCheckApplies() && !BypassTickDataCheck;
        }

        /// <summary>
        /// Runs on every completed signal bar. Two cheap measurements:
        ///   1. Bar-to-bar discontinuity. A back-adjusted continuous contract has
        ///      essentially none; raw per-contract data jumps by the roll spread
        ///      four times a year. Gaps are logged with dates so the quarterly
        ///      pattern is visible rather than inferred.
        ///   2. A fingerprint over a FIXED calendar window, so two installations
        ///      can be compared directly no matter how much history each loaded.
        /// </summary>
        private void ScanBarForDataIntegrity(DateTime barEnd)
        {
            try
            {
                if (_firstBarTime == DateTime.MaxValue) _firstBarTime = barEnd;
                if (_prevSigClose > 0)
                {
                    double gap = Math.Abs(_bOpen - _prevSigClose);
                    if (gap >= ROLL_GAP_PTS)
                    {
                        _gapCount++;
                        if (gap > _worstGap) _worstGap = gap;
                        int mm = barEnd.Month;
                        if (mm == 3 || mm == 6 || mm == 9 || mm == 12) _gapsInRollMonths++;
                        if (_gapCount <= 8)
                            _gapList += "       " + barEnd.ToString("yyyy-MM-dd")
                                      + "   " + gap.ToString("N2") + " pts\n";
                    }
                }
                _prevSigClose = _bClose;

                if (barEnd.Year == FP_YEAR && barEnd.Month == FP_MONTH)
                {
                    long t = (long)Math.Round(_bClose * 4.0);   // price in ticks
                    for (int i = 0; i < 8; i++)
                    {
                        _fpHash ^= (ulong)((t >> (i * 8)) & 0xFF);
                        _fpHash *= 1099511628211UL;
                    }
                    _fpBars++;
                }
            }
            catch { }
        }

        /// <summary>Soft hint only. Repeated large gaps in roll months SUGGEST raw
        /// per-contract data, but legitimate Sunday-open gaps overlap the same
        /// magnitude range, so this never raises the warning on its own.</summary>
        private bool DataLooksUnadjusted()
        {
            return _gapCount >= 2 && _gapsInRollMonths >= 2;
        }

        private string FingerprintHex()
        {
            return _fpBars == 0 ? "" : (_fpHash & 0xFFFFFFFFUL).ToString("X8");
        }

        /// <summary>-1 = cannot compare, 0 = mismatch, 1 = match.</summary>
        private int FingerprintVerdict()
        {
            if (_fpBars == 0 || EXPECTED_FP.Length == 0) return -1;
            return string.Equals(FingerprintHex(), EXPECTED_FP, StringComparison.OrdinalIgnoreCase) ? 1 : 0;
        }

        private void ReportDataIntegrity()
        {
            try
            {
                Print("");
                Print("  DATA INTEGRITY");
                Print("  Signal bars built      : " + _barsBuilt.ToString("N0") + " x " + _periodMin + "-min");
                Print("  Price discontinuities  : " + _gapCount
                      + "  (threshold " + ROLL_GAP_PTS.ToString("N0") + " pts)"
                      + (_gapCount > 0 ? "   worst " + _worstGap.ToString("N2") + " pts" : ""));
                if (_gapCount > 0)
                {
                    Print(_gapList.TrimEnd('\n'));
                    if (_gapCount > 8) Print("       ... and " + (_gapCount - 8) + " more");
                }
                if (DataLooksUnadjusted())
                    Print("  Roll pattern           : ⚠ " + _gapsInRollMonths + " of " + _gapCount
                          + " gaps fall in roll months — POSSIBLY raw per-contract data"
                          + " (not conclusive on its own)");

                int v = FingerprintVerdict();
                string fp = FingerprintHex();
                Print("  Fingerprint (" + FP_YEAR + "-" + FP_MONTH.ToString("00") + ")  : "
                      + (fp.Length == 0 ? "n/a — no bars loaded in that window" : fp + "  over " + _fpBars + " bars")
                      + (v == 1 ? "   ✓ MATCHES reference" : v == 0 ? "   ✗ DOES NOT MATCH reference (" + EXPECTED_FP + ")" : ""));
                if (v < 0 && fp.Length > 0 && EXPECTED_FP.Length == 0)
                    Print("                           No reference embedded in this build — compare manually.");

                if (v == 0 && !_dataMessageBoxShown)
                {
                    _dataMessageBoxShown = true;
                    ShowMessageBox(
                        "OCTVERSION2 — Your Price Data Does Not Match Ours\n\n"
                      + "Your data fingerprint :  " + fp + "\n"
                      + "Expected              :  " + EXPECTED_FP + "\n"
                      + "Window                :  " + FP_YEAR + "-" + FP_MONTH.ToString("00")
                      + "   (" + _fpBars + " bars)\n"
                      + "History starts        :  " + (_firstBarTime == DateTime.MaxValue
                                                        ? "(none)" : _firstBarTime.ToString("yyyy-MM-dd"))
                      + "\nRequired              :  ≤ 2025-01-01\n"
                      + (_gapCount > 0 ? "Discontinuities       :  " + _gapCount
                                         + "   (worst " + _worstGap.ToString("N2") + " pts, "
                                         + _gapsInRollMonths + " in roll months)\n" : "")
                      + "\nYour price series differs from the one these results were produced on.\n"
                      + "Signals are rebuilt from your own tick data, so a different series gives a\n"
                      + "different trade list. Your results are NOT comparable to the published ones.\n\n"
                      + "MOST COMMON CAUSE: NQ imported as separate per-contract files\n"
                      + "(NQ 03-25, 06-25, 09-25, 12-25) instead of one continuous contract.\n"
                      + "That makes prices step by the roll spread every quarter.\n\n"
                      + "FIX\n"
                      + "  1. NinjaTrader -> Tools -> Instruments -> NQ -> set merge policy to\n"
                      + "     'Merge Back Adjusted'. Remove any per-contract .txt imports.\n"
                      + "  2. Load history back past 2025-01-01 (2024 is better).\n"
                      + "  3. Restart the strategy and check this box is gone.",
                        "OCTVERSION2 — Price Data Mismatch",
                        System.Windows.MessageBoxImage.Warning);
                }
            }
            catch (Exception ex) { Print("[GHOST] ReportDataIntegrity exception: " + ex.Message); }
        }

        private void EvaluateFirstTrade()
        {
            if (_firstTradeCheckDone) return;
            _firstTradeCheckDone = true;

            // The history GATE can be bypassed or not apply to this tier, but the data
            // integrity report always runs — bad data is bad data regardless of tier.
            if (BypassTickDataCheck)
            {
                _historyAdequate = true;
                Print("------------------------------------------------");
                Print("  POST-HISTORICAL DATA CHECK");
                Print("------------------------------------------------");
                Print("  History gate           : ⚠ BYPASSED BY USER (BypassTickDataCheck = true)");
                ReportDataIntegrity();
                Print("------------------------------------------------");
                PaintAllChrome();
                return;
            }
            if (!HistoryCheckApplies())
            {
                _historyAdequate = true;
                Print("------------------------------------------------");
                Print("  POST-HISTORICAL DATA CHECK");
                Print("------------------------------------------------");
                Print("  History gate           : not required for " + ModeName());
                ReportDataIntegrity();
                Print("------------------------------------------------");
                PaintAllChrome();
                return;
            }

            try
            {
                DateTime historyAsOf;
                string   historyLabel;
                if (_isMicroMode && BarsArray.Length > _signalBip && BarsArray[_signalBip] != null && BarsArray[_signalBip].Count > 0)
                {
                    historyAsOf  = BarsArray[_signalBip].GetTime(0);
                    historyLabel = "NQ tick history starts";
                }
                else if (_firstTradeTime != DateTime.MaxValue)
                {
                    historyAsOf  = _firstTradeTime;
                    historyLabel = "First trade entry time";
                }
                else
                {
                    // No trade ever fired. Judge the DATA on the data, not on the
                    // absence of trades, otherwise a legitimately quiet period reads
                    // as missing history.
                    historyAsOf  = _firstBarTime;
                    historyLabel = "First signal bar built ";
                }
                _historyAdequate = historyAsOf <= MIN_REQUIRED_HISTORY;

                int tradeCount = (SystemPerformance != null && SystemPerformance.AllTrades != null)
                                    ? SystemPerformance.AllTrades.Count : 0;
                Print("------------------------------------------------");
                Print("  POST-HISTORICAL DATA CHECK");
                Print("------------------------------------------------");
                Print("  Historical trade count : " + tradeCount);
                Print("  " + historyLabel + " : " + historyAsOf.ToString("yyyy-MM-dd HH:mm:ss"));
                Print("  Required               : ≤ 2025-01-01");
                Print("  Verdict                : " + (_historyAdequate ? "✓ OK — data is sufficient"
                                                                        : "✗ INSUFFICIENT — source data is after 2025-01-01"));
                ReportDataIntegrity();
                Print("------------------------------------------------");

                if (!_historyAdequate && !_historyMessageBoxShown)
                {
                    _historyMessageBoxShown = true;
                    ShowMessageBox("OCTVERSION2 — You Need More Tick Data\n\n"
                        + historyLabel + " : " + historyAsOf.ToString("yyyy-MM-dd HH:mm") + "\n"
                        + "Required : ≤ 2025-01-01\n\n"
                        + "Live trading is BLOCKED until the tick history reaches back far enough —\n"
                        + "otherwise the signal threshold is under-calibrated.\n\n"
                        + "FIX: import NQ tick data from Databento with the DatabentoConverter tool,\n"
                        + "then restart the strategy with more days loaded.",
                        "OCTVERSION2 — You Need More Tick Data", System.Windows.MessageBoxImage.Warning);
                }
                PaintAllChrome();
            }
            catch (Exception ex) { Print("[GHOST] EvaluateFirstTrade exception: " + ex.Message); }
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  INIT + LOGGING
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private void InitRuntimeState()
        {
            askVol = new Dictionary<double, long>();
            bidVol = new Dictionary<double, long>();
            lastPrice = 0;
            barBigDeltaCount = 0;
            cumDelta = cumDeltaMax = cumDeltaMin = 0;
            prevPOC = 0; prevPOCValid = false; contDownCount = 0;

            bdcFreq      = new SortedList<double, int>(); bdcTotal = 0;
            dmFreq       = new SortedList<double, int>(); dmTotal  = 0;
            bsicFreq     = new SortedList<double, int>(); bsicTotal= 0;
            bodySizeFreq = new SortedList<double, int>(); bodySizeTotal = 0;

            _curBucket = -1; _firstBarPartial = true; _barsBuilt = 0;
            barsProcessed = 0; totalTicks = 0;
            signalsFiredLong = signalsFiredShort = 0;
            qualifyingBarsLong = qualifyingBarsShort = 0;
            _frozenBars = _newsBars = 0;
            _inLong = _inShort = false;
        }

        private void LogStartupBanner()
        {
            bool tiers = _mode != Mode.Paragon;
            Print("================================================");
            string suffix = "";
            if (_armed && !_tfOk) suffix = " (DATA SERIES MUST BE 1 TICK → forced DORMANT)";
            Print("  OCTVERSION2 LOADED — " + (_armed ? "ARMED" : "DORMANT") + suffix);
            Print("================================================");
            Print("  Edition     : " + ModeName());
            if (_armed)
            {
                Print("  Signal bars : " + _periodMin + "-minute, built internally from the tick stream");
                Print("  Bracket     : SL " + _slPts + " / " + (_useLadder ? "point ladder (no fixed target)" : ("TP " + _tpPts)) + " pts (locked)");
                if (UseStopLimitExit)
                    Print("  ⚠ Exit mode : STOP-LIMIT (no-slip) + fallback " + StopLimitFallbackPts + " pt");
                else
                    Print("  Exit mode   : managed stop/target on the tick series");
                Print("  Front-run   : " + (FrontRunEnabled ? ("ON  lock " + LockBeforeMs + "ms / fire " + EnterBeforeMs + "ms before close") : "OFF"));
                if (tiers)
                {
                    Print("  News skip   : " + (SkipNews ? ("ON  +/-" + NewsWindowMins + "m around " + NewsSlotsLabel()) : "OFF"));
                    Print("  Daily freeze: ON (HARDCODED) — no new entries 14:55 → 17:15 CT (+ session-end branch)");
                }
                else
                    Print("  News / freeze: not used by Paragon (same as the Paragon product)");
                if (HistoryCheckApplies())
                    Print("  Data check  : " + (BypassTickDataCheck ? "⚠ BYPASSED by user" : "runs after historical processing (needs history ≤ 2025-01-01)"));
            }
            else
            {
                Print("  REASON      : " + _failureReason);
            }
            Print("  Data series : " + _currentTfLabel + (_tfOk ? "  ✓" : "  ✗ must be 1 Tick"));
            Print("  Instrument  : " + (Instrument != null ? Instrument.FullName : "(null)")
                  + (_isMicroMode ? "  (MNQ BRIDGE — signals from " + _nqContractSym + " ticks, execution on MNQ)" : ""));
            Print("  Version     : " + STRATEGY_VERSION);
            try
            {
                Bars sb = BarsArray[_signalBip];
                if (sb != null && sb.Count > 1)
                {
                    DateTime t0 = sb.GetTime(0), t1 = sb.GetTime(sb.Count - 1);
                    Print("  Ticks loaded: " + sb.Count.ToString("N0") + "  (" + t0.ToString("yyyy-MM-dd") + " → " + t1.ToString("yyyy-MM-dd")
                          + ", ~" + ((t1 - t0).TotalDays * 23.0 * 5.0 / 7.0 * 60.0 / _periodMin).ToString("N0")
                          + " " + _periodMin + "-min bars; warmup needs " + WARMUP_BARS + ")");
                }
            }
            catch { }
            Print("================================================");
        }

        private void LogTerminationSummary()
        {
            Print("================================================");
            Print("  OCTVERSION2 TERMINATED");
            Print("================================================");
            Print("  Final state    : " + (_armed ? (_tfOk ? "ARMED" : "DORMANT (data series)") : "DORMANT"));
            Print("  Mode           : " + ModeName());
            Print("  Signal bars    : " + _barsBuilt.ToString("N0") + " x " + _periodMin + "-min   ticks: " + totalTicks.ToString("N0"));
            if (_mode != Mode.Paragon)
                Print("  Bars skipped   : freeze=" + _frozenBars + "  news=" + _newsBars);
            Print("  Signals fired  : long=" + signalsFiredLong + "  short=" + signalsFiredShort);
            try
            {
                if (SystemPerformance != null && SystemPerformance.AllTrades != null && SystemPerformance.AllTrades.Count > 0)
                {
                    Print("  Trades closed  : " + SystemPerformance.AllTrades.Count);
                    Print("  Realized PnL   : $" + SystemPerformance.AllTrades.TradesPerformance.Currency.CumProfit.ToString("N2"));
                    Print("  Profit factor  : " + SystemPerformance.AllTrades.TradesPerformance.ProfitFactor.ToString("F2"));
                }
            }
            catch { }
            Print("================================================");
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  EVERY TICK
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        protected override void OnBarUpdate()
        {
            try
            {
                if (!_initDone) return;

                // EXECUTION instrument tick: ladder ratchet + stop-limit fallback.
                if (BarsInProgress == 0)
                {
                    if (_useLadder && _ladActive) LadderUpdate(Close[0]);
                    if (UseStopLimitExit) ManageStopFallback(Close[0]);
                }

                // SIGNAL tick (same series as execution on NQ; the NQ series under MNQ).
                if (BarsInProgress != _signalBip) return;
                if (!_tfOk)
                {
                    if (!_tfWarned) { _tfWarned = true; Print("[GHOST] DORMANT — data series is " + _currentTfLabel + ", must be 1 Tick."); }
                    return;
                }
                if (!_bridgeViable) return;

                OnSignalTick(Close[0], (long)Volume[0], Time[0]);
            }
            catch (Exception ex) { Print("[GHOST] OnBarUpdate exception: " + ex.Message); }
        }

        private void OnSignalTick(double px, long vol, DateTime t)
        {
            // Internal bar. (Ticks - 1): a tick stamped exactly on the boundary belongs to the
            // bar that ENDS there, like NinjaTrader's own minute bars.
            long span   = _periodMin * TimeSpan.TicksPerMinute;
            long bucket = (t.Ticks - 1) / span;
            if (_curBucket == -1)
            {
                _curBucket = bucket; _bOpen = px; _bHigh = px; _bLow = px;
            }
            else if (bucket != _curBucket)
            {
                OnSignalBarClosed(new DateTime((_curBucket + 1) * span));
                ClearBarTickState();
                _curBucket = bucket; _bOpen = px; _bHigh = px; _bLow = px;
            }
            _bClose = px;
            if (px > _bHigh) _bHigh = px;
            if (px < _bLow || _bLow <= 0) _bLow = px;
            _snBarVolume += vol;

            if (_armed && UsesFootprint()) HandleTick(px, vol);

            if (FrontRunEnabled && _armed && !HistoryBlocksEntries())
                FrontRunTick(px, t);
        }

        private bool UsesFootprint()
        {
            // After the v2.0 tier swap the NOISE-BAND engine sits on ENHANCED, and it
            // needs only price, volume and the clock - no bid/ask classification. The
            // DELTA/POC engine moved to STANDARD and does need the footprint.
            return _mode == Mode.Standard || _mode == Mode.Ultimate;
        }

        // v1.3.0 HandleTick — tick-rule classification, big-delta count, cum-delta range.
        private void HandleTick(double price, long v)
        {
            totalTicks++;
            double p = SnapToTick(price);
            bool classified = false;
            long deltaTick = 0;

            if (price > lastPrice)
            {
                askVol[p] = askVol.TryGetValue(p, out long a) ? a + v : v;
                classified = true;
                deltaTick  = v;
            }
            else if (price < lastPrice)
            {
                bidVol[p] = bidVol.TryGetValue(p, out long b) ? b + v : v;
                classified = true;
                deltaTick  = -v;
            }
            else
            {
                askVol[p] = askVol.TryGetValue(p, out long a) ? a + v / 2 : v / 2;
                bidVol[p] = bidVol.TryGetValue(p, out long b) ? b + v - v / 2 : v - v / 2;
            }

            if (classified && v >= BIG_DELTA_TICK) barBigDeltaCount++;

            cumDelta += deltaTick;
            if (cumDelta > cumDeltaMax) cumDeltaMax = cumDelta;
            if (cumDelta < cumDeltaMin) cumDeltaMin = cumDelta;
            lastPrice = price;
        }

        private void ClearBarTickState()
        {
            _snBarVolume = 0;
            askVol.Clear();
            bidVol.Clear();
            barBigDeltaCount = 0;
            cumDelta = cumDeltaMax = cumDeltaMin = 0;
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  SIGNAL BAR CLOSED — v1.3.0 bar-close path. barEnd plays the role of Time[0].
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private void OnSignalBarClosed(DateTime barEnd)
        {
            // The first bar after start-up begins mid-bar — not a real bar.
            if (_firstBarPartial) { _firstBarPartial = false; return; }
            _barsBuilt++;
            barsProcessed++;
            ScanBarForDataIntegrity(barEnd);

            if (UseStopLimitExit) ManageStopFallback(ExecLastPrice());   // bar-close backup

            // GATE 1: run state (only MNQ bridge failure can disarm)
            if (!_armed)
            {
                if (barsProcessed % 250 == 0)
                {
                    Print("[OCTVERSION2] DORMANT — bar " + barEnd + " (" + _failureReason + ")");
                    PaintAllChrome();
                }
                return;
            }

            // GATE 2: history adequacy
            if (HistoryBlocksEntries())
            {
                _historyDormantLogCount++;
                if (_historyDormantLogCount <= 3 || _historyDormantLogCount % 500 == 0)
                {
                    Print("[GHOST] DORMANT — first historical trade was "
                          + (_firstTradeTime == DateTime.MaxValue ? "(none)" : _firstTradeTime.ToString("yyyy-MM-dd"))
                          + ", required ≤ 2025-01-01. Import more tick data and restart.");
                    PaintAllChrome();
                }
                return;
            }

            // Before any gate: Standard must be flat outside its session.
            SN_FlattenIfDue(barEnd);

            if (_mode == Mode.Paragon)
            {
                BarLogic_Paragon();          // Paragon: no freeze, no news — same as the Paragon product
            }
            else
            {
                CheckFreezeTransition(barEnd);
                bool freezeNow = IsInDailyFreeze(barEnd);
                if (freezeNow)
                {
                    _frozenBars++;
                    LogFreezeBlockedAttempt("bar-close dispatcher", barEnd);
                }
                else if (InNewsWindow(barEnd))
                {
                    _newsBars++;
                }
                else
                {
                    switch (_mode)
                    {
                        case Mode.Standard:    BarLogic_DeltaPoc();        break;
                        case Mode.Enhanced:    BarLogic_NoiseBand(barEnd); break;
                        case Mode.Elite:       BarLogic_Elite();       break;
                        case Mode.Ultimate:    BarLogic_Ultimate();    break;
                    }
                }
            }

            if (barsProcessed % PANEL_REFRESH_N == 0) PaintAllChrome();
        }

        private double ExecLastPrice()
        {
            try { return Closes[0][0]; } catch { return 0; }
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  ENTRY — one place for every mode and both entry paths
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private void SubmitEntry(int dir, double refPx, string features)
        {
            if (_barsBuilt < BARS_REQUIRED) return;                 // v1.3.0 BarsRequiredToTrade
            bool bidir = _mode == Mode.Paragon ? PAR_BIDIR : ENABLE_BIDIR;
            if (dir > 0)
            {
                qualifyingBarsLong++;
                SnapshotSignal(_entryLongTag, refPx);
                EnterLong(0, Quantity, _entryLongTag);
                signalsFiredLong++;
                OnSignalEntry(true, refPx);
            }
            else if (dir < 0 && bidir)
            {
                qualifyingBarsShort++;
                SnapshotSignal(_entryShortTag, refPx);
                EnterShort(0, Quantity, _entryShortTag);
                signalsFiredShort++;
                OnSignalEntry(false, refPx);
            }
        }

        private void OnSignalEntry(bool isLong, double price)
        {
            _entryPrice = price;
            _inLong     = isLong;
            _inShort    = !isLong;
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  TIER LOGIC — rules byte-for-byte from GhostAlgo v1.3.0 / Paragon 1.0.0
        //  (SigOpen/SigClose → the internal bar's open/close)
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private bool CanEnterAtClose()
        {
            return !FrontRunEnabled && ExecPos.MarketPosition == MarketPosition.Flat;
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  STANDARD — noise-band intraday momentum
        //
        //  sigma(m) = mean over the last 14 sessions of |close(m) / RTH open - 1|.
        //  upper = max(open, prior close) * (1 + mult*sigma)
        //  lower = min(open, prior close) * (1 - mult*sigma)
        //  Every 30 minutes while flat: close above upper AND above VWAP -> long;
        //  close below lower AND below VWAP -> short. Bracket is volatility scaled:
        //  stop = max(4, 0.16 * average RTH daily range), target = 2 x stop.
        //  Max 5 entries a day, last entry 15:30 ET, flat by 15:58 ET.
        //
        //  Unlike every other mode here this one is FLAT OVERNIGHT by design, so
        //  the freeze window and the session-end branch never have a position to
        //  deal with. That is the point of it.
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private void SN_RollSession(DateTime barEnd)
        {
            // Fold today's deviations into the rolling sigma history, then reset.
            foreach (var kv in _snTodayDev)
            {
                List<double> hist;
                if (!_snSigmaHist.TryGetValue(kv.Key, out hist))
                {
                    hist = new List<double>();
                    _snSigmaHist[kv.Key] = hist;
                }
                hist.Add(kv.Value);
                if (hist.Count > SN_LOOKBACK_DAYS) hist.RemoveAt(0);
            }
            _snTodayDev.Clear();

            if (_snDayHigh > 0 && _snDayLow > 0 && _snDayHigh > _snDayLow)
            {
                _snDayRanges.Add(_snDayHigh - _snDayLow);
                if (_snDayRanges.Count > SN_LOOKBACK_DAYS) _snDayRanges.RemoveAt(0);
            }

            if (!double.IsNaN(_snLastRthClose)) _snPrevRthClose = _snLastRthClose;

            _snSessionOpen = false;
            _snTradesToday = 0;
            _snSumPV = _snSumV = 0;
            _snDayHigh = _snDayLow = 0;
            _snRthOpen = 0;
        }

        private double SN_Sigma(int minuteOffset)
        {
            List<double> hist;
            if (!_snSigmaHist.TryGetValue(minuteOffset, out hist) || hist.Count < SN_LOOKBACK_DAYS)
                return double.NaN;                       // not warmed up for this minute yet
            double sum = 0;
            for (int i = 0; i < hist.Count; i++) sum += hist[i];
            return sum / hist.Count;
        }

        private double SN_AvgDailyRange()
        {
            if (_snDayRanges.Count == 0) return double.NaN;
            double sum = 0;
            for (int i = 0; i < _snDayRanges.Count; i++) sum += _snDayRanges[i];
            return sum / _snDayRanges.Count;
        }

        // Flat before the bell, every day, no exceptions.
        //
        // This MUST run outside the freeze gate. The daily freeze is 14:55-17:15 CT
        // and it skips the whole bar-close dispatcher, so the original flatten at
        // 14:58 sat inside the frozen window and never fired once in 1,005 trades:
        // 59 of them rode overnight and others exited at 17:00-23:00 on a stop.
        // The freeze exists to stop NEW risk being opened, not to trap a position
        // that the strategy has already decided to close.
        private void SN_FlattenIfDue(DateTime barEnd)
        {
            // v2.0 tier swap: the noise band moved to ENHANCED. If this guard is left
            // pointing at Standard the session flatten never fires for the tier that
            // actually needs it, and positions ride overnight - the exact failure the
            // comment above describes.
            if (_mode != Mode.Enhanced)                          return;
            if (ExecPos.MarketPosition == MarketPosition.Flat)   return;

            // Hold only inside the trading window; flat everywhere else.
            TimeSpan tod = barEnd.TimeOfDay;
            if (tod > SN_RTH_OPEN && tod < SN_FLATTEN)           return;

            try
            {
                if (ExecPos.MarketPosition == MarketPosition.Long)
                    ExitLong(0, Math.Abs(ExecPos.Quantity), "SN Flat", _entryLongTag);
                else
                    ExitShort(0, Math.Abs(ExecPos.Quantity), "SN Flat", _entryShortTag);
            }
            catch { }
        }

        private void BarLogic_NoiseBand(DateTime barEnd)
        {
            TimeSpan tod = barEnd.TimeOfDay;

            // Outside RTH: close the session the first time we see a bar past the bell.
            if (tod <= SN_RTH_OPEN || tod > SN_RTH_CLOSE)
            {
                if (_snSessionOpen && tod > SN_RTH_CLOSE) SN_RollSession(barEnd);
                return;
            }

            // New RTH day.
            if (_snDate != barEnd.Date)
            {
                if (_snSessionOpen) SN_RollSession(barEnd);
                _snDate        = barEnd.Date;
                _snSessionOpen = true;
                _snRthOpen     = _bOpen > 0 ? _bOpen : _bClose;
                _snDayHigh     = _bHigh;
                _snDayLow      = _bLow;
            }

            if (_snRthOpen <= 0) return;

            // Session state. Volume is the internal bar's, accumulated on the tick series.
            // True extremes from the tick stream, not bar closes. On bar data this
            // range is always understated, which quietly shrinks every stop.
            if (_bHigh > _snDayHigh) _snDayHigh = _bHigh;
            if (_bLow  < _snDayLow || _snDayLow <= 0) _snDayLow = _bLow;
            double barVol = _snBarVolume > 0 ? _snBarVolume : 1;
            _snSumPV += _bClose * barVol;
            _snSumV  += barVol;
            _snLastRthClose = _bClose;

            int m = (int)Math.Round((tod - SN_RTH_OPEN).TotalMinutes);
            if (m <= 0) return;
            _snTodayDev[m] = Math.Abs(_bClose / _snRthOpen - 1.0);

            // The flatten itself lives in SN_FlattenIfDue, hoisted above the freeze
            // gate in OnSignalBarClosed. Here we only stop opening new risk.
            if (tod >= SN_FLATTEN) return;

            if (tod > SN_LAST_ENTRY)                       return;
            if (m % SN_CHECK_MINUTES != 0)                 return;   // half-hour grid only
            if (_snTradesToday >= SN_MAX_TRADES_DAY)       return;
            if (!CanEnterAtClose())                        return;

            double sigma = SN_Sigma(m);
            if (double.IsNaN(sigma) || sigma <= 0)         return;
            if (double.IsNaN(_snPrevRthClose))             return;   // need a prior close
            if (_snSumV <= 0)                              return;

            double vwap  = _snSumPV / _snSumV;
            double hiRef = Math.Max(_snRthOpen, _snPrevRthClose);
            double loRef = Math.Min(_snRthOpen, _snPrevRthClose);
            double upper = hiRef * (1.0 + SN_BAND_MULT * sigma);
            double lower = loRef * (1.0 - SN_BAND_MULT * sigma);

            int dir = 0;
            if (_bClose >= upper && _bClose > vwap)      dir =  1;
            else if (_bClose <= lower && _bClose < vwap) dir = -1;
            if (dir == 0) return;

            // Volatility scaled bracket, recomputed per trade.
            double adr  = SN_AvgDailyRange();
            double stop = Math.Max(SN_MIN_STOP_POINTS,
                                   double.IsNaN(adr) ? SN_MIN_STOP_POINTS : SN_BRACKET_ATR * adr);
            _slPts = stop;
            _tpPts = SN_REWARD_RISK * stop;
            SetupBrackets();

            _snTradesToday++;
            SubmitEntry(dir, _bClose, "sn");
        }

        // The pre-October Standard: 15-minute big-delta microscalper. Replaced as the
        // default Standard edge but kept verbatim so it can be switched back on.
                // 1h BodySize bidir, FIXED cutoff, no warmup (Standard licence + toggle).
                // DeltaMove_q5 ∧ NOT HasBearContPOC
        private void BarLogic_DeltaPoc()
        {
            if (askVol.Count == 0 && bidVol.Count == 0) return;

            long   deltaMove = cumDeltaMax - cumDeltaMin;
            double poc       = ComputePOC();
            if (prevPOCValid && poc < prevPOC) contDownCount++;
            else                                contDownCount = 0;
            bool hasBearContPOC = contDownCount >= POC_CONT_DOWN_BARS;

            int    barDir     = Math.Sign(_bClose - _bOpen);
            bool   warmupDone = dmTotal >= WARMUP_BARS;
            double q80        = warmupDone ? Quantile(dmFreq, dmTotal, QUANTILE_LEVEL) : double.NaN;
            bool   isDmQ5     = warmupDone && (deltaMove >= q80);
            bool   ruleFires  = isDmQ5 && !hasBearContPOC;

            if (warmupDone && ruleFires && barDir != 0 && CanEnterAtClose())
                SubmitEntry(barDir, _bClose, "enh");
            AddToFreq(dmFreq, ref dmTotal, deltaMove);
            prevPOC      = poc;
            prevPOCValid = true;
        }

        private void BarLogic_Elite()
        {
            double bodySize   = Math.Abs(_bClose - _bOpen);
            int    barDir     = Math.Sign(_bClose - _bOpen);
            bool   warmupDone = bodySizeTotal >= WARMUP_BARS;
            double q80        = warmupDone ? Quantile(bodySizeFreq, bodySizeTotal, QUANTILE_LEVEL) : double.NaN;
            bool   isQ5       = warmupDone && (bodySize >= q80);

            if (warmupDone && isQ5 && barDir != 0 && CanEnterAtClose())
                SubmitEntry(barDir, _bClose, "eli");
            AddToFreq(bodySizeFreq, ref bodySizeTotal, bodySize);
        }

        // BigSellImbCount_q5 ∧ BigDeltaCount_q5
        private void BarLogic_Ultimate()
        {
            if (askVol.Count == 0 && bidVol.Count == 0) return;
            int bigDeltaCount         = barBigDeltaCount;
            int bigSellImbalanceCount = BigSellImbalanceCount();

            int    barDir     = Math.Sign(_bClose - _bOpen);
            bool   warmupDone = (bsicTotal >= WARMUP_BARS) && (bdcTotal >= WARMUP_BARS);
            double q80_bsic   = warmupDone ? Quantile(bsicFreq, bsicTotal, QUANTILE_LEVEL) : double.NaN;
            double q80_bdc    = warmupDone ? Quantile(bdcFreq,  bdcTotal,  QUANTILE_LEVEL) : double.NaN;
            bool   ruleFires  = warmupDone && bigSellImbalanceCount >= q80_bsic && bigDeltaCount >= q80_bdc;

            if (ruleFires && barDir != 0 && CanEnterAtClose())
                SubmitEntry(barDir, _bClose, "ult");
            AddToFreq(bsicFreq, ref bsicTotal, bigSellImbalanceCount);
            AddToFreq(bdcFreq,  ref bdcTotal,  bigDeltaCount);
        }

        // Paragon: 1h BodySize top 10%, 1000-bar warmup, every bar counted.
        private void BarLogic_Paragon()
        {
            double bodySize   = Math.Abs(_bClose - _bOpen);
            int    barDir     = Math.Sign(_bClose - _bOpen);
            bool   warmupDone = bodySizeTotal >= PAR_WARMUP;
            double q          = warmupDone ? Quantile(bodySizeFreq, bodySizeTotal, PAR_QUANTILE) : double.NaN;
            bool   isQ        = warmupDone && (bodySize >= q);

            if (warmupDone && isQ && barDir != 0 && CanEnterAtClose())
                SubmitEntry(barDir, _bClose, "par");
            AddToFreq(bodySizeFreq, ref bodySizeTotal, bodySize);
        }

        private int BigSellImbalanceCount()
        {
            int n = 0;
            foreach (var p in bidVol.Keys)
            {
                long bh = bidVol[p];
                if (bh <= 0) continue;
                double pDown = SnapToTick(p - TickSize);
                long ad = askVol.TryGetValue(pDown, out long av) ? av : 0L;
                double sr = ad > 0 ? ((double)bh / ad) : 99.0;
                if (sr >= IMBALANCE_RATIO) n++;
            }
            return n;
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  FRONT-RUN — lock / fire before the internal bar's clock close
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private void FrontRunTick(double px, DateTime nowT)
        {
            try
            {
                int P = _periodMin;
                DateTime day = nowT.Date;
                int idx = (int)Math.Floor((nowT - day).TotalMinutes / P);
                DateTime barOpenTime  = day.AddMinutes(idx * (double)P);
                DateTime barCloseTime = barOpenTime.AddMinutes(P);
                double msToClose = (barCloseTime - nowT).TotalMilliseconds;

                if (barOpenTime != _frBarOpenTime)
                {
                    _frBarOpenTime = barOpenTime;
                    _frBarOpen     = px;
                    _frLocked = false; _frEntered = false;
                    _frDecisionReady = false; _frDecisionShouldTrade = false; _frDecisionDir = 0;
                }
                if (_frEntered)    return;
                if (msToClose < 0) return;

                if (!_frLocked && msToClose <= LockBeforeMs) FrDecideEntry((int)msToClose, nowT, px);
                if (msToClose <= EnterBeforeMs)
                {
                    if (!_frLocked) FrDecideEntry((int)msToClose, nowT, px);
                    FrExecuteEntry((int)msToClose, nowT, px);
                }
            }
            catch (Exception ex) { Print("[GHOST][FR] exception: " + ex.Message); }
        }

        private void FrDecideEntry(int msToClose, DateTime nowT, double px)
        {
            int dir = EvaluatePartialSignal(px);
            _frDecisionDir         = dir;
            _frDecisionShouldTrade = dir != 0;
            _frDecisionReady       = true;
            _frLocked              = true;
            if (FrontRunLogs)
                Print("[GHOST][FR] FREEZE/DECIDE " + nowT + " msToClose=" + msToClose
                      + " trade=" + _frDecisionShouldTrade + " dir=" + _frDecisionDir);
        }

        private void FrExecuteEntry(int msToClose, DateTime nowT, double px)
        {
            lock (_entryLock)
            {
                if (_frEntered) return;
                _frEntered = true;
            }
            if (!_armed || !_tfOk || HistoryBlocksEntries()) return;
            if (!_frDecisionReady || !_frDecisionShouldTrade) return;
            if (ExecPos.MarketPosition != MarketPosition.Flat) return;
            if (_mode != Mode.Paragon)
            {
                if (InNewsWindow(nowT))
                {
                    if (FrontRunLogs) Print("[GHOST] ENTRY BLOCKED @ " + nowT.ToString("HH:mm:ss") + " - inside a news-skip window");
                    return;
                }
                if (IsInDailyFreeze(nowT)) { LogFreezeBlockedAttempt("FrontRun FrExecuteEntry", nowT); return; }
            }
            SubmitEntry(_frDecisionDir, px, "frontrun");
            if (FrontRunLogs)
                Print("[GHOST][FR] EXECUTE " + (_frDecisionDir > 0 ? "LONG" : "SHORT") + " " + nowT
                      + " @ " + px.ToString("F2") + " msToClose=" + msToClose);
        }

        // Active mode's rule on the CURRENT partial bar, prior-bar quantiles only.
        private int EvaluatePartialSignal(double cur)
        {
            try
            {
                double barOpen = _frBarOpen;
                int    barDir  = Math.Sign(cur - barOpen);
                if (barDir == 0) return 0;

                switch (_mode)
                {
                    case Mode.Standard:
                    {
                        // v2.0 swap: the delta/POC engine lives on STANDARD now, and it
                        // IS front-runnable because the signal forms inside the bar.
                        if (dmTotal < WARMUP_BARS) return 0;
                        long   deltaMove = cumDeltaMax - cumDeltaMin;
                        double q80       = Quantile(dmFreq, dmTotal, QUANTILE_LEVEL);
                        double poc       = ComputePOC();
                        int    provDown  = (prevPOCValid && poc < prevPOC) ? (contDownCount + 1) : 0;
                        return (deltaMove >= q80 && provDown < POC_CONT_DOWN_BARS) ? barDir : 0;
                    }
                    case Mode.Enhanced:
                        // v2.0 swap: the noise band lives on ENHANCED now. Entries are
                        // decided on a half-hour clock grid at bar close, so there is no
                        // forming-bar signal to front-run, and it does not accumulate the
                        // footprint this branch would read.
                        return 0;
                    case Mode.Elite:
                    {
                        if (bodySizeTotal < WARMUP_BARS) return 0;
                        double q80 = Quantile(bodySizeFreq, bodySizeTotal, QUANTILE_LEVEL);
                        return Math.Abs(cur - barOpen) >= q80 ? barDir : 0;
                    }
                    case Mode.Ultimate:
                    {
                        if (bsicTotal < WARMUP_BARS || bdcTotal < WARMUP_BARS) return 0;
                        double q80b = Quantile(bsicFreq, bsicTotal, QUANTILE_LEVEL);
                        double q80d = Quantile(bdcFreq,  bdcTotal,  QUANTILE_LEVEL);
                        return (BigSellImbalanceCount() >= q80b && barBigDeltaCount >= q80d) ? barDir : 0;
                    }
                    case Mode.Paragon:
                    {
                        if (bodySizeTotal < PAR_WARMUP) return 0;
                        double q = Quantile(bodySizeFreq, bodySizeTotal, PAR_QUANTILE);
                        if (Math.Abs(cur - barOpen) < q) return 0;
                        if (barDir < 0 && !PAR_BIDIR) return 0;
                        return barDir;
                    }
                }
                return 0;
            }
            catch { return 0; }
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  DAILY FREEZE (v1.3.0) — Ghost tiers only
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private bool IsInDailyFreeze(DateTime now)
        {
            return IsInDailyFreezeBySession(now) || IsInDailyFreezeByCtClock(now);
        }

        private bool IsInDailyFreezeBySession(DateTime now)
        {
            try
            {
                if (_closeGuardSessionIter == null) return false;
                _closeGuardSessionIter.CalculateTradingDay(now, true);
                double minToNext = (_closeGuardSessionIter.ActualSessionEnd - now).TotalMinutes;
                if (minToNext >= 0 && minToNext <= FREEZE_PRECLOSE_MIN) return true;

                DateTime lookback = now.AddMinutes(-(FREEZE_POSTEND_MIN + 10));
                _closeGuardSessionIter.CalculateTradingDay(lookback, true);
                DateTime endFromLookback = _closeGuardSessionIter.ActualSessionEnd;
                if (endFromLookback > lookback && endFromLookback <= now)
                {
                    double minSinceEnd = (now - endFromLookback).TotalMinutes;
                    if (minSinceEnd >= 0 && minSinceEnd <= FREEZE_POSTEND_MIN) return true;
                }
                return false;
            }
            catch { return false; }
        }

        private bool IsInDailyFreezeByCtClock(DateTime now)
        {
            int nowMin = now.Hour * 60 + now.Minute;
            return nowMin >= FREEZE_CT_START_MIN && nowMin < FREEZE_CT_END_MIN;
        }

        private void LogFreezeBlockedAttempt(string source, DateTime now)
        {
            try
            {
                if (now.Date != _freezeBlocksLogResetDay) { _freezeBlocksLogResetDay = now.Date; _freezeBlocksLoggedToday = 0; }
                if (_freezeBlocksLoggedToday >= 5) return;
                _freezeBlocksLoggedToday++;
                Print("[GHOST] ⛔ FREEZE blocked entry attempt @ " + now.ToString("yyyy-MM-dd HH:mm:ss") + "  via " + source
                      + "  (session-branch=" + IsInDailyFreezeBySession(now) + ", ct-clock-branch=" + IsInDailyFreezeByCtClock(now) + ")");
            }
            catch { }
        }

        private void CheckFreezeTransition(DateTime now)
        {
            try
            {
                try
                {
                    if (_closeGuardSessionIter != null)
                    {
                        _closeGuardSessionIter.CalculateTradingDay(now, true);
                        DateTime sessEnd = _closeGuardSessionIter.ActualSessionEnd;
                        if (sessEnd.Date != _freezeDiagPrintedForDay)
                        {
                            _freezeDiagPrintedForDay = sessEnd.Date;
                            Print("[GHOST] Freeze window for " + sessEnd.ToString("yyyy-MM-dd")
                                  + " :  start " + sessEnd.AddMinutes(-FREEZE_PRECLOSE_MIN).ToString("HH:mm")
                                  + "  →  end " + sessEnd.AddMinutes(FREEZE_POSTEND_MIN).ToString("HH:mm")
                                  + "  (session-end anchor = " + sessEnd.ToString("HH:mm") + ", chart-local time)");
                        }
                    }
                }
                catch { }

                bool nowFrozen = IsInDailyFreeze(now);
                if (nowFrozen && !_freezeActive)
                {
                    _freezeActive = true;
                    Print("[GHOST] ⛔ DAILY FREEZE engaged @ " + now.ToString("yyyy-MM-dd HH:mm") + " — no new entries.");
                    CancelPendingEntries();
                    DrawFreezeOverlay(true);
                }
                else if (!nowFrozen && _freezeActive)
                {
                    _freezeActive = false;
                    Print("[GHOST] ✓ Daily freeze LIFTED @ " + now.ToString("yyyy-MM-dd HH:mm") + " — strategy resumed.");
                    DrawFreezeOverlay(false);
                }
            }
            catch { }
        }

        private void CancelPendingEntries()
        {
            try
            {
                if (Orders == null) return;
                int cancelled = 0;
                foreach (var o in Orders.ToArray())
                {
                    if (o == null) continue;
                    if (o.OrderState != OrderState.Working && o.OrderState != OrderState.Accepted
                        && o.OrderState != OrderState.Submitted) continue;
                    if (o.Name != _entryLongTag && o.Name != _entryShortTag) continue;
                    try { CancelOrder(o); cancelled++; } catch { }
                }
                if (cancelled > 0) Print("[GHOST] Cancelled " + cancelled + " pending entry order(s) at freeze engage.");
            }
            catch { }
        }

        private void DrawFreezeOverlay(bool active)
        {
            try
            {
                if (active)
                {
                    int startMin = (16 * 60) - FREEZE_PRECLOSE_MIN;
                    int endMin   = (16 * 60) + FREEZE_POSTEND_MIN;
                    string text = "⛔ DAILY FREEZE ACTIVE\n"
                                + (startMin / 60).ToString("D2") + ":" + (startMin % 60).ToString("D2") + " → "
                                + (endMin / 60).ToString("D2") + ":" + (endMin % 60).ToString("D2") + " CT\n"
                                + "No new entries\n" + STRATEGY_VERSION;
                    Draw.TextFixed(this, FREEZE_OVERLAY_TAG, text, TextPosition.Center,
                        Brushes.White, new SimpleFont("Arial", 16) { Bold = true }, Brushes.Red, Brushes.DarkRed, 80);
                }
                else
                {
                    try { RemoveDrawObject(FREEZE_OVERLAY_TAG); } catch { }
                }
            }
            catch { }
        }

        // NEWS SKIP — +/- NewsWindowMins around each configured HHmm (chart clock). Fail-open.
        private bool InNewsWindow(DateTime now)
        {
            if (!SkipNews) return false;
            try
            {
                double nowMin = now.TimeOfDay.TotalMinutes;
                foreach (int s in new[] { NewsTime1, NewsTime2, NewsTime3, NewsTime4, NewsTime5 })
                {
                    if (s <= 0) continue;
                    int hh = s / 100, mm = s % 100;
                    if (hh > 23 || mm > 59) continue;
                    if (Math.Abs(nowMin - (hh * 60 + mm)) <= NewsWindowMins) return true;
                }
            }
            catch { return false; }
            return false;
        }

        private string NewsSlotsLabel()
        {
            var sb = new StringBuilder();
            foreach (int s in new[] { NewsTime1, NewsTime2, NewsTime3, NewsTime4, NewsTime5 })
                if (s > 0) sb.Append((s / 100).ToString("D2") + ":" + (s % 100).ToString("D2") + " ");
            return sb.Length == 0 ? "(none set)" : sb.ToString().Trim();
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  STOP-LIMIT FALLBACK — compared against EXECUTION-instrument prices
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private void ManageStopFallback(double cp)
        {
            try
            {
                if (!_sleExitPlaced) return;
                if (ExecPos.MarketPosition == MarketPosition.Flat) { _sleExitPlaced = false; _sleStopPrice = 0; return; }
                if (StopLimitFallbackPts <= 0 || _sleStopPrice <= 0 || cp <= 0) return;
                if (_sleLong && cp <= _sleStopPrice - StopLimitFallbackPts)
                {
                    ExitLong(0, ExecPos.Quantity, "StopFallback", "");
                    if (FrontRunLogs) Print("[GHOST][SLE] stop-limit unfilled, price " + cp.ToString("F2") + " past stop -> MARKET out");
                    _sleExitPlaced = false; _sleStopPrice = 0;
                }
                else if (!_sleLong && cp >= _sleStopPrice + StopLimitFallbackPts)
                {
                    ExitShort(0, ExecPos.Quantity, "StopFallback", "");
                    if (FrontRunLogs) Print("[GHOST][SLE] stop-limit unfilled, price " + cp.ToString("F2") + " past stop -> MARKET out");
                    _sleExitPlaced = false; _sleStopPrice = 0;
                }
            }
            catch (Exception ex) { Print("[GHOST][SLE] fallback ex: " + ex.Message); }
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  ORDER REJECTION HANDLER + CIRCUIT BREAKER (v1.3.0)
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        protected override void OnOrderUpdate(Order order, double limitPrice, double stopPrice,
            int quantity, int filled, double averageFillPrice,
            OrderState orderState, DateTime time, ErrorCode error, string nativeError)
        {
            if (LogExecutionLatency && order != null)
            {
                try { LogOrderEventToLatencyCsv(order, orderState, error, nativeError, limitPrice, stopPrice, quantity, filled, averageFillPrice); }
                catch { }
            }

            try
            {
                if (order == null) return;
                bool isExplicitRejection = orderState == OrderState.Rejected;
                bool hasBrokerErrorCode  = error != ErrorCode.NoError && error != ErrorCode.UserAbort;
                bool hasNativeMessage    = !string.IsNullOrEmpty(nativeError)
                                        && orderState != OrderState.Filled && orderState != OrderState.PartFilled;
                if (!isExplicitRejection && !hasBrokerErrorCode && !hasNativeMessage) return;

                int nowTick = Environment.TickCount;
                bool isOurFlatten = order.Name != null
                                 && order.Name.IndexOf("RejectFlatten", StringComparison.OrdinalIgnoreCase) >= 0;

                if (nowTick < _circuitBreakerUntilTick)
                {
                    if (!_circuitBreakerAnnounced)
                    {
                        _circuitBreakerAnnounced = true;
                        Print("[GHOST] ⛔ CIRCUIT BREAKER — halting rejection-response logic for "
                              + ((_circuitBreakerUntilTick - nowTick) / 1000) + "s. Position may be exposed — check the broker UI.");
                    }
                    return;
                }
                _circuitBreakerAnnounced = false;

                if (nowTick - _rejectionBurstWindowStartTick > BURST_WINDOW_MS)
                {
                    _rejectionBurstWindowStartTick = nowTick;
                    _rejectionBurstCount = 0;
                }
                _rejectionBurstCount++;
                if (_rejectionBurstCount > BURST_THRESHOLD)
                {
                    _circuitBreakerUntilTick = nowTick + CIRCUIT_BREAK_MS;
                    _circuitBreakerAnnounced = false;
                    Print("[GHOST] ⛔ Burst threshold exceeded (" + _rejectionBurstCount + " rejections in "
                          + (BURST_WINDOW_MS / 1000) + "s) — circuit breaker open for " + (CIRCUIT_BREAK_MS / 1000) + "s.");
                    return;
                }

                double price = stopPrice > 0 ? stopPrice : limitPrice;
                Print("[GHOST] ⚠ ORDER FAILED — " + order.Name + "  type=" + order.OrderType + "  action=" + order.OrderAction
                      + "  state=" + orderState + "  price=" + price.ToString("F2") + "  qty=" + quantity);
                if (error != ErrorCode.NoError)        Print("[GHOST]   error code  : " + error);
                if (!string.IsNullOrEmpty(nativeError)) Print("[GHOST]   broker msg  : " + nativeError);

                if (isOurFlatten)
                {
                    Print("[GHOST] Rejected order was our RejectFlatten — NOT submitting another.");
                    return;
                }
                if (nowTick < _rejectionFlattenCooldownUntilTick)
                {
                    Print("[GHOST] Within flatten cooldown — skipping re-flatten.");
                    return;
                }

                if (ExecPos.MarketPosition != MarketPosition.Flat)
                {
                    _rejectionFlattenCooldownUntilTick = nowTick + FLATTEN_COOLDOWN_MS;
                    Print("[GHOST] Flattening position with market order to recover.");
                    try
                    {
                        if (ExecPos.MarketPosition == MarketPosition.Long)
                            ExitLong(0, Math.Abs(ExecPos.Quantity), "RejectFlatten", _entryLongTag);
                        else
                            ExitShort(0, Math.Abs(ExecPos.Quantity), "RejectFlatten", _entryShortTag);
                    }
                    catch (Exception inner) { Print("[GHOST] Flatten exception: " + inner.Message); }
                }
                Print("[GHOST] Strategy continues — armed for next signal.");
            }
            catch (Exception ex) { Print("[GHOST] OnOrderUpdate exception: " + ex.Message); }
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  EXECUTION HANDLER
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        protected override void OnExecutionUpdate(Execution execution, string executionId, double price,
            int quantity, MarketPosition marketPosition, string orderId, DateTime time)
        {
            if (execution == null || execution.Order == null) return;

            // NUCLEAR FREEZE BACKSTOP (Ghost tiers): an entry that fills inside the freeze is flattened.
            try
            {
                bool isEntryFill = !execution.IsExit && execution.Order.Name != null
                                && (execution.Order.Name == _entryLongTag || execution.Order.Name == _entryShortTag);
                if (isEntryFill && _mode != Mode.Paragon && IsInDailyFreeze(time))
                {
                    Print("[GHOST] ⚠⚠ NUCLEAR BACKSTOP — entry filled DURING FREEZE @ " + time
                          + " price=" + price.ToString("F2") + " — flattening immediately.");
                    if (marketPosition == MarketPosition.Long)
                        ExitLong(0, Math.Abs(ExecPos.Quantity), "FreezeFlatten", _entryLongTag);
                    else if (marketPosition == MarketPosition.Short)
                        ExitShort(0, Math.Abs(ExecPos.Quantity), "FreezeFlatten", _entryShortTag);
                }
            }
            catch (Exception ex) { Print("[GHOST] FreezeFlatten failed: " + ex.Message); }

            // First-trade tracker for the history gate.
            if (!_firstTradeRecorded && !execution.IsExit && HistoryCheckApplies())
            {
                _firstTradeRecorded = true;
                _firstTradeTime     = time;
                if (State == State.Realtime && !_firstTradeCheckDone) EvaluateFirstTrade();
            }

            try
            {
                if (execution.IsExit)
                {
                    bool   wasLong  = _inLong;
                    double ptDelta  = wasLong ? (price - _entryPrice) : (_entryPrice - price);
                    double ptValue  = 20.0;
                    try { if (Instrument != null && Instrument.MasterInstrument != null) ptValue = Instrument.MasterInstrument.PointValue; } catch { }
                    double pnl = ptDelta * ptValue * Math.Max(1, quantity);

                    LadderReset();
                    _inLong = _inShort = false;
                    _sleExitPlaced = false; _sleStopPrice = 0;
                    PaintAllChrome();

                    Print("[GHOST] EXIT  " + (wasLong ? "LONG " : "SHORT") + " " + time + " @ " + price.ToString("F2")
                          + "  qty=" + quantity + "  (" + execution.Order.Name + ")  " + (pnl >= 0 ? "WIN" : "LOSS")
                          + "  $" + pnl.ToString("N2"));
                }
                else
                {
                    LadderOnEntryFill(price, marketPosition == MarketPosition.Long);
                    Print("[GHOST] ENTRY " + marketPosition + " " + time + " @ " + price.ToString("F2") + "  qty=" + quantity);

                    if (UseStopLimitExit && !_sleExitPlaced
                        && ExecPos.MarketPosition != MarketPosition.Flat && ExecPos.Quantity >= Quantity)
                    {
                        double rp = ExecPos.AveragePrice; if (rp <= 0) rp = price;
                        bool islong = marketPosition == MarketPosition.Long;
                        double sp = islong ? rp - _slPts : rp + _slPts;
                        double tp = islong ? rp + _tpPts : rp - _tpPts;
                        try
                        {
                            if (islong)
                            {
                                ExitLongStopLimit(0, true, ExecPos.Quantity, sp, sp, "StopLoss", "");
                                ExitLongLimit    (0, true, ExecPos.Quantity, tp,     "TakeProfit", "");
                            }
                            else
                            {
                                ExitShortStopLimit(0, true, ExecPos.Quantity, sp, sp, "StopLoss", "");
                                ExitShortLimit    (0, true, ExecPos.Quantity, tp,     "TakeProfit", "");
                            }
                            _sleStopPrice = sp; _sleLong = islong; _sleExitPlaced = true;
                            if (FrontRunLogs) Print("[GHOST][SLE] stop-limit @ " + sp.ToString("F2") + "  TP @ " + tp.ToString("F2"));
                        }
                        catch (Exception ex) { Print("[GHOST][SLE] place ex: " + ex.Message); }
                    }
                }
            }
            catch { }
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  LATENCY LOGGING (opt-in)
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private void SnapshotSignal(string entryTag, double sigPx)
        {
            if (!LogExecutionLatency) return;
            try
            {
                _signalTimeByEntryTag[entryTag]  = DateTime.Now;
                _signalPriceByEntryTag[entryTag] = sigPx;
                LatencyLog("signal_log.csv",
                    "time,strategy,mode,account,instrument,entry_tag,direction,signal_price,quantity,version",
                    CsvRow(DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss.fff"), "OCTVERSION2", ModeName(),
                           Account != null ? Account.Name : "unknown",
                           Instrument != null ? Instrument.FullName : "unknown",
                           entryTag, entryTag == _entryLongTag ? "Long" : "Short",
                           sigPx, Quantity, STRATEGY_VERSION));
            }
            catch { }
        }

        private void LogOrderEventToLatencyCsv(Order order, OrderState orderState, ErrorCode error, string nativeError,
            double limitPrice, double stopPrice, int quantity, int filled, double averageFillPrice)
        {
            string lookupTag = !string.IsNullOrEmpty(order.FromEntrySignal) ? order.FromEntrySignal : order.Name;
            DateTime signalTime = DateTime.MinValue;
            double   signalPrice = 0;
            if (lookupTag != null)
            {
                _signalTimeByEntryTag.TryGetValue(lookupTag,  out signalTime);
                _signalPriceByEntryTag.TryGetValue(lookupTag, out signalPrice);
            }
            LatencyLog("order_event_log.csv",
                "time,strategy,mode,account,instrument,order_id,order_name,order_role,action,type,"
              + "quantity,filled,limit_price,stop_price,avg_fill,state,error_code,native_error,"
              + "signal_time,signal_price,tick_size,version",
                CsvRow(DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss.fff"), "OCTVERSION2", ModeName(),
                       Account != null ? Account.Name : "unknown",
                       Instrument != null ? Instrument.FullName : "unknown",
                       order.OrderId ?? "", order.Name ?? "", ClassifyOrder(order.Name),
                       order.OrderAction, order.OrderType, quantity, filled,
                       limitPrice, stopPrice, averageFillPrice, orderState, error,
                       nativeError ?? "",
                       signalTime == DateTime.MinValue ? "" : signalTime.ToString("yyyy-MM-dd HH:mm:ss.fff"),
                       signalPrice,
                       (Instrument != null && Instrument.MasterInstrument != null) ? Instrument.MasterInstrument.TickSize : 0.25,
                       STRATEGY_VERSION));
        }

        private static string ClassifyOrder(string name)
        {
            string n = (name ?? "").ToLowerInvariant();
            if (n.Contains("target") || n.Contains("profit")) return "Target";
            if (n.Contains("stop"))                          return "Stop";
            if (n.Contains("entry"))                         return "Entry";
            if (n.Contains("exit"))                          return "Exit";
            return "Other";
        }

        private static string CsvRow(params object[] values)
        {
            var sb = new StringBuilder();
            for (int i = 0; i < values.Length; i++)
            {
                if (i > 0) sb.Append(',');
                string s = values[i] == null
                    ? ""
                    : Convert.ToString(values[i], System.Globalization.CultureInfo.InvariantCulture);
                if (s.IndexOfAny(new[] { ',', '"', '\n', '\r' }) >= 0)
                    s = "\"" + s.Replace("\"", "\"\"") + "\"";
                sb.Append(s);
            }
            return sb.ToString();
        }

        private static readonly object _latencyLogLock = new object();

        private static void LatencyLog(string fileName, string header, string row)
        {
            try
            {
                string dir = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments),
                                          "NinjaTrader 8", "latency");
                if (!Directory.Exists(dir)) Directory.CreateDirectory(dir);
                string path = Path.Combine(dir, fileName);
                lock (_latencyLogLock)
                {
                    bool needHeader = !File.Exists(path);
                    using (var sw = new StreamWriter(path, true, Encoding.UTF8))
                    {
                        if (needHeader) sw.WriteLine(header);
                        sw.WriteLine(row);
                    }
                }
            }
            catch { }
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  UI — status text + message boxes (skipped with no UI thread)
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private void PaintAllChrome()
        {
            try
            {
                string status;
                if (!_armed)                      status = "DORMANT (bridge)";
                else if (!_tfOk)                  status = "DORMANT (data series must be 1 Tick)";
                else if (HistoryBlocksEntries())  status = "DORMANT (history)";
                else                              status = "ARMED";
                Draw.TextFixed(this, "ghost_status", "OCTVERSION2  " + ModeName() + "  -  " + status, TextPosition.TopRight);
            }
            catch { }
        }

        private void ShowMessageBox(string text, string title, System.Windows.MessageBoxImage icon)
        {
            try
            {
                var app = System.Windows.Application.Current;
                if (app == null) return;
                app.Dispatcher.BeginInvoke(new Action(() =>
                {
                    try { System.Windows.MessageBox.Show(text, title, System.Windows.MessageBoxButton.OK, icon); }
                    catch { }
                }));
            }
            catch { }
        }

        private void ShowTfMismatchMessageBox()
        {
            ShowMessageBox(
                "OCTVERSION2 — Wrong Data Series\n\n"
              + "Current data series :  " + _currentTfLabel + "\n"
              + "Required            :  1 Tick\n\n"
              + "This version builds its own " + _periodMin + "-minute signal bars from the tick stream,\n"
              + "so it must run on a 1-TICK series (chart, Strategies tab or Strategy Analyzer).\n\n"
              + "Fix: set the data series to Type = Tick, Value = 1, then re-enable.",
                "OCTVERSION2 — Wrong Data Series", System.Windows.MessageBoxImage.Warning);
        }

                // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        //  MATH + HTTP HELPERS
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        private double SnapToTick(double price) { return Math.Round(price / TickSize) * TickSize; }

        private double ComputePOC()
        {
            double poc = 0; long max = 0;
            foreach (var p in askVol.Keys.Union(bidVol.Keys))
            {
                long v = (askVol.TryGetValue(p, out long a) ? a : 0L) + (bidVol.TryGetValue(p, out long b) ? b : 0L);
                if (v > max) { max = v; poc = p; }
            }
            return poc;
        }

        private static void AddToFreq(SortedList<double, int> freq, ref int total, double v)
        {
            if (freq.ContainsKey(v)) freq[v]++;
            else                     freq.Add(v, 1);
            total++;
        }

        private static double Quantile(SortedList<double, int> freq, int total, double q)
        {
            if (freq.Count == 0 || total == 0) return double.NaN;
            long target = (long)Math.Ceiling(q * total);
            long cum = 0;
            for (int i = 0; i < freq.Count; i++)
            {
                cum += freq.Values[i];
                if (cum >= target) return freq.Keys[i];
            }
            return freq.Keys[freq.Count - 1];
        }

        //  PROPERTIES
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        [NinjaScriptProperty]
        [Display(Name = "Edition",
                 Description = "Which rule set to run. Standard = delta/POC, 60-min bars, SL 10 / TP 30. "
                             + "Enhanced = noise-band, 1-min bars, volatility bracket. Elite = 60-min, SL 3 / TP 18. "
                             + "Ultimate = 60-min, SL 10 + point ladder. Paragon = 60-min, SL 10 / TP 24, no news filter, no daily freeze. "
                             + "Run on a 1-TICK data series (NQ or MNQ). "
                             + "Setup: 'Exit on session close' OFF, 'Max restart attempts' 25, 'Start behavior' Wait until flat.",
                 Order = 1, GroupName = "1. Strategy")]
        public AlgoEdition Edition { get; set; }

        [NinjaScriptProperty]
        [Range(1, 100)]
        [Display(Name = "Contracts per trade",
                 Description = "1–100. Risk = SL points × contracts × point value (NQ $20/pt, MNQ $2/pt).",
                 Order = 2, GroupName = "1. Strategy")]
        public int Quantity { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Bypass tick data check",
                 Description = "ADVANCED — leave OFF. Skips the ≤ 2025-01-01 tick-history check.",
                 Order = 3, GroupName = "1. Strategy")]
        public bool BypassTickDataCheck { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Log execution latency",
                 Description = "DIAGNOSTIC — only if support asks. Writes signal + order-event rows to Documents\\NinjaTrader 8\\latency\\.",
                 Order = 4, GroupName = "1. Strategy")]
        public bool LogExecutionLatency { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Front-run enabled", Description = "Fire intrabar BEFORE the signal bar's close instead of at close. OFF = original behavior.", Order = 1, GroupName = "2. FrontRun")]
        public bool FrontRunEnabled { get; set; }

        [NinjaScriptProperty, Range(0, 60000)]
        [Display(Name = "Lock before close (ms)", Description = "Freeze the decision this many ms before close. Recommended 3000.", Order = 2, GroupName = "2. FrontRun")]
        public int LockBeforeMs { get; set; }

        [NinjaScriptProperty, Range(0, 60000)]
        [Display(Name = "Enter before close (ms)", Description = "How many ms before close to FIRE. Set to ~your order-routing latency (usually 500-600ms). Must be <= Lock-before.", Order = 3, GroupName = "2. FrontRun")]
        public int EnterBeforeMs { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Front-run verbose logs", Order = 4, GroupName = "2. FrontRun")]
        public bool FrontRunLogs { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use stop-limit exit — only if you have slippage", Description = "⚠ ENABLE ONLY IF YOU ACTUALLY GET SLIPPAGE ON STOPS. ON = exits as stop-limit (no-slip) + limit TP; the fallback below markets you out if the limit is skipped. Turns the point ladder off.", Order = 1, GroupName = "3. ExitLimit")]
        public bool UseStopLimitExit { get; set; }

        [NinjaScriptProperty, Range(0, 200.0)]
        [Display(Name = "Stop-limit fallback (pts) — 0 = NO fallback", Description = "Only with 'Use stop-limit exit'. 0 = never force-closed (risky). 0.25 = next tick (recommended).", Order = 2, GroupName = "3. ExitLimit")]
        public double StopLimitFallbackPts { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Skip news times (master ON/OFF)", Description = "VERY IMPORTANT. No new entry within +/- the window of any news time below. Not used by the Paragon edition.", Order = 1, GroupName = "4. NEWS - VERY IMPORTANT (read tooltips)")]
        public bool SkipNews { get; set; }

        [NinjaScriptProperty, Range(0, 30)]
        [Display(Name = "News window (+/- mins)", Description = "Blocks entries this many minutes before and after each news time.", Order = 2, GroupName = "4. NEWS - VERY IMPORTANT (read tooltips)")]
        public int NewsWindowMins { get; set; }

        [NinjaScriptProperty, Range(0, 2359)]
        [Display(Name = "News time 1  (HHmm, 0=off)", Description = "Central time. FOMC 2pm ET = 1300 | CPI/NFP/PPI 8:30am ET = 0730 | daily close = 1600.", Order = 3, GroupName = "4. NEWS - VERY IMPORTANT (read tooltips)")]
        public int NewsTime1 { get; set; }

        [NinjaScriptProperty, Range(0, 2359)]
        [Display(Name = "News time 2  (HHmm, 0=off)", Description = "Central time. 0 = off.", Order = 4, GroupName = "4. NEWS - VERY IMPORTANT (read tooltips)")]
        public int NewsTime2 { get; set; }

        [NinjaScriptProperty, Range(0, 2359)]
        [Display(Name = "News time 3  (HHmm, 0=off)", Description = "Central time. 0 = off.", Order = 5, GroupName = "4. NEWS - VERY IMPORTANT (read tooltips)")]
        public int NewsTime3 { get; set; }

        [NinjaScriptProperty, Range(0, 2359)]
        [Display(Name = "News time 4  (HHmm, 0=off)", Description = "Central time. 0 = off.", Order = 6, GroupName = "4. NEWS - VERY IMPORTANT (read tooltips)")]
        public int NewsTime4 { get; set; }

        [NinjaScriptProperty, Range(0, 2359)]
        [Display(Name = "News time 5  (HHmm, 0=off)", Description = "Central time. 0 = off.", Order = 7, GroupName = "4. NEWS - VERY IMPORTANT (read tooltips)")]
        public int NewsTime5 { get; set; }
    }
} 

