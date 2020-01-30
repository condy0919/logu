//! A lightweight logger.
//!
//! The `Logger` provides a single logging API that abstracts over the actual log
//! sinking implementation.
//!
//! A log request consists of a _level_ and a _message_.
//!
//! # Use
//!
//! The basic logging of the `Logger` is through the following macros:
//!
//! - [`emerge!`] system is unusable
//! - [`alert!`] action must be taken immediately
//! - [`crit!`] critical conditions
//! - [`error!`] error conditions
//! - [`warn!`] warning conditions
//! - [`notice!`] normal, but significant, condition
//! - [`info!`] informational message
//! - [`debug!`] debug-level message
//!
//! The log messages are filtered by configuring the log level to exclude
//! message with lower priority.
//!
//! # Example
//!
//! ```
//! [macro_use]
//! extern crate logu;
//!
//! use std::io;
//!
//! pub fn foo() {
//!     let mut stdout = io::stdout();
//!     let mut logger = log::Logger::new(log::Level::Info, &mut stdout);
//!
//!     info!(logger, "foo");
//! }
//! ```
//!
//! # Log format
//!
//! Every log message obeys the following fixed and easily-parsable format:
//!
//! ```text
//! YYYY-mm-dd HH:MM:SS.mss [level] <file>:<line> <message>\n
//! ```
//!
//! - `YYYY` denotes years to *4* digits, any message having year larger than
//! 9999 will be ignored
//! - `mm` denotes monthes zero-padded to *2* digits
//! - `dd` denotes days zero-padded to *2* digits
//! - `HH` denotes hours zero-padded to *2* digits
//! - `MM` denotes minutes zero-padded to *2* digits
//! - `SS` denotes seconds zero-padded to *2* digits
//! - `mss` denotes milliseconds zero-padded to *3* digits
//! - `level` is the log level as defined by `Level`
//! - `message` is the log message
//!
//! # Errors
//!
//! Any errors returned by the sink when writing are ignored.
//!

use std::error;
use std::fmt;
use std::io;
use std::str::FromStr;
use std::time::{SystemTime, UNIX_EPOCH};

/// The standard logging macro.
///
/// This macro will generically log with the specified `Level` and arguments list.
///
/// # Example
///
/// ```
/// #[macro_use]
/// extern crate logu;
///
/// use logu::log;
/// use std::io;
///
/// # fn main() {
/// let mut stderr = io::stderr();
/// let mut logger = log::Logger::new(log::Level::Debug, &mut strerr);
///
/// log!(logger, log::Level::Error, "{}", 123);
/// # }
/// ```
#[macro_export]
macro_rules! log {
    ($logger:expr, $lvl:expr, $($arg:tt)+) => {
        $logger.log($lvl, file!(), line!(), format_args!($($arg)+));
    }
}

/// Logs a message at the emerge level
#[macro_export]
macro_rules! emerge {
    ($logger:expr, $($arg:tt)+) => {
        log!($logger, $crate::log::Level::Emerge, $($arg)+);
    };
}

/// Logs a message at the alert level
#[macro_export]
macro_rules! alert {
    ($logger:expr, $($arg:tt)+) => {
        log!($logger, $crate::log::Level::Alert, $($arg)+);
    };
}

/// Logs a message at the critical level
#[macro_export]
macro_rules! crit {
    ($logger:expr, $($arg:tt)+) => {
        log!($logger, $crate::log::Level::Critical, $($arg)+);
    };
}

/// Logs a message at the error level
#[macro_export]
macro_rules! error {
    ($logger:expr, $($arg:tt)+) => {
        log!($logger, $crate::log::Level::Error, $($arg)+);
    };
}

/// Logs a message at the warning level
#[macro_export]
macro_rules! warn {
    ($logger:expr, $($arg:tt)+) => {
        log!($logger, $crate::log::Level::Warning, $($arg)+);
    };
}

/// Logs a message at the notice level
#[macro_export]
macro_rules! notice {
    ($logger:expr, $($arg:tt)+) => {
        log!($logger, $crate::log::Level::Notice, $($arg)+);
    };
}

/// Logs a message at the informative level
#[macro_export]
macro_rules! info {
    ($logger:expr, $($arg:tt)+) => {
        log!($logger, $crate::log::Level::Info, $($arg)+);
    };
}

/// Logs a message at the debug level
#[macro_export]
macro_rules! debug {
    ($logger:expr, $($arg:tt)+) => {
        log!($logger, $crate::log::Level::Debug, $($arg)+);
    };
}

/// A format optimized Logger
pub struct Logger<'a> {
    filter: Level,
    writer: &'a mut dyn io::Write,
    last_ts: u64,
    buffer: [u8; 4096],
}

impl<'a> Logger<'a> {
    /// Constructs a `Logger` instance with specified `Level` and io backed
    /// writer.
    #[inline]
    pub fn new(filter: Level, writer: &'a mut dyn io::Write) -> Logger {
        Logger {
            filter,
            writer,
            last_ts: 0,
            buffer: [0u8; 4096],
        }
    }

    /// Sets the logger log level
    #[inline]
    pub fn set_level(&mut self, level: Level) {
        self.filter = level;
    }

    /// Logs the message
    pub fn log<'r>(
        &mut self,
        level: Level,
        file: &'static str,
        mut line: u32,
        args: fmt::Arguments<'r>,
    ) {
        if level > self.filter {
            return;
        }

        let dur = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
        let secs_since_epoch = dur.as_secs();
        let msec = dur.subsec_millis();

        if secs_since_epoch >= 253402300800u64 {
            panic!("cannot format year 9999");
        }

        let (year, mon, day, hr, min, sec) = seal::localtime(secs_since_epoch);

        // cache to reduce the number of format operations
        if self.last_ts != secs_since_epoch {
            self.last_ts = secs_since_epoch;

            // years
            self.buffer[0] = b'0' + (year / 1000) as u8;
            self.buffer[1] = b'0' + (year / 100 % 10) as u8;
            self.buffer[2] = b'0' + (year / 10 % 100) as u8;
            self.buffer[3] = b'0' + (year % 10) as u8;

            self.buffer[4] = b'-';

            // months
            self.buffer[5] = b'0' + (mon / 10) as u8;
            self.buffer[6] = b'0' + (mon % 10) as u8;

            self.buffer[7] = b'-';

            // days
            self.buffer[8] = b'0' + (day / 10) as u8;
            self.buffer[9] = b'0' + (day % 10) as u8;

            self.buffer[10] = b' ';

            // hours
            self.buffer[11] = b'0' + (hr / 10) as u8;
            self.buffer[12] = b'0' + (hr % 10) as u8;

            self.buffer[13] = b':';

            // minutes
            self.buffer[14] = b'0' + (min / 10) as u8;
            self.buffer[15] = b'0' + (min % 10) as u8;

            self.buffer[16] = b':';

            // seconds
            self.buffer[17] = b'0' + (sec / 10) as u8;
            self.buffer[18] = b'0' + (sec % 10) as u8;
            self.buffer[19] = b'.';
        }

        // milliseconds
        self.buffer[20] = b'0' + (msec / 100) as u8;
        self.buffer[21] = b'0' + (msec / 10 % 10) as u8;
        self.buffer[22] = b'0' + (msec % 10) as u8;
        self.buffer[23] = b' ';

        self.buffer[24] = b'[';

        let len = LOG_LEVEL_NAMES[level as usize].len();
        self.buffer[25..][..len].copy_from_slice(LOG_LEVEL_NAMES[level as usize].as_bytes());

        let mut idx = 25 + len;

        self.buffer[idx] = b']';
        idx += 1;

        self.buffer[idx] = b' ';
        idx += 1;

        self.buffer[idx..][..file.len()].copy_from_slice(file.as_bytes());
        idx += file.len();

        self.buffer[idx] = b':';
        idx += 1;

        let digits_begin = idx;
        loop {
            self.buffer[idx] = b'0' + ((line % 10) as u8);
            idx += 1;

            line /= 10;
            if line == 0 {
                break;
            }
        }
        self.buffer[digits_begin..idx].reverse();

        self.buffer[idx] = b' ';
        idx += 1;

        let _ = self.writer.write(&self.buffer[0..idx]);
        let _ = self.writer.write_fmt(args);
        let _ = self.writer.write(b"\n");
    }
}

/// The type returned by [`from_str`] when the string doesn't match any of the
/// log levels.
///
/// [`from_str`]: https://doc.rust-lang.org/std/str/trait.FromStr.html#tymethod.from_str
#[derive(Debug, PartialEq)]
pub struct LevelParseError;

impl fmt::Display for LevelParseError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str("parse log level error")
    }
}

impl error::Error for LevelParseError {}

/// An enum representing the available verbosity levels of the logger.
///
/// Typical usage includes: specifying the `Level` of `log!`, and comparing a
/// `Level` directly to `Level`
#[repr(usize)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum Level {
    /// The "none" level.
    ///
    /// No loggin
    None = 0,
    /// The "emerge" level.
    ///
    /// System is unusable
    Emerge,
    /// The "alert" level
    ///
    /// Action must be take immediately
    Alert,
    /// The "crit" level
    ///
    /// Critical conditions
    Critical,
    /// The "error" level
    ///
    /// Error conditions
    Error,
    /// The "warn" level
    ///
    /// Warning conditions
    Warning,
    /// The "notice" level
    ///
    /// Normal, but significant condition
    Notice,
    /// The "info" level
    ///
    /// Information
    Info,
    /// The "debug" level
    ///
    /// Debug messages
    Debug,
}

static LOG_LEVEL_NAMES: [&str; 9] = [
    "NONE", "EMERGE", "ALERT", "CRITICAL", "ERROR", "WARNING", "NOTICE", "INFO", "DEBUG",
];

impl fmt::Display for Level {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(LOG_LEVEL_NAMES[*self as usize])
    }
}

impl From<usize> for Level {
    fn from(l: usize) -> Self {
        match l {
            0 => Level::None,
            1 => Level::Emerge,
            2 => Level::Alert,
            3 => Level::Critical,
            4 => Level::Error,
            5 => Level::Warning,
            6 => Level::Notice,
            7 => Level::Info,
            8 => Level::Debug,
            _ => panic!("Unknown Level"),
        }
    }
}

impl FromStr for Level {
    type Err = LevelParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let opt = LOG_LEVEL_NAMES
            .iter()
            .position(|&name| -> bool {
                if name.len() != s.len() {
                    return false;
                }

                // case insensitive
                s.bytes()
                    .zip(name.bytes())
                    .all(|(a, b)| (a | 0x20) == (b | 0x20))
            })
            .into_iter()
            .map(|idx| Level::from(idx))
            .next();

        match opt {
            Some(o) => Ok(o),
            None => Err(LevelParseError),
        }
    }
}

mod seal {
    // Stolen from https://github.com/tailhook/humantime/blob/8b8d748566c85a73b2f940e755dc0160c93f465a/src/date.rs
    pub fn localtime(secs: u64) -> (u32, u32, u32, u32, u32, u32) {
        /* 2000-03-01 (mod 400 year, immediately after feb29 */
        const LEAPOCH: i64 = 11017;
        const DAYS_PER_400Y: i64 = 365 * 400 + 97;
        const DAYS_PER_100Y: i64 = 365 * 100 + 24;
        const DAYS_PER_4Y: i64 = 365 * 4 + 1;

        let days = (secs / 86400) as i64 - LEAPOCH;
        let secs_of_day = secs % 86400;

        let mut qc_cycles = days / DAYS_PER_400Y;
        let mut remdays = days % DAYS_PER_400Y;

        if remdays < 0 {
            remdays += DAYS_PER_400Y;
            qc_cycles -= 1;
        }

        let mut c_cycles = remdays / DAYS_PER_100Y;
        if c_cycles == 4 {
            c_cycles -= 1;
        }
        remdays -= c_cycles * DAYS_PER_100Y;

        let mut q_cycles = remdays / DAYS_PER_4Y;
        if q_cycles == 25 {
            q_cycles -= 1;
        }
        remdays -= q_cycles * DAYS_PER_4Y;

        let mut remyears = remdays / 365;
        if remyears == 4 {
            remyears -= 1;
        }
        remdays -= remyears * 365;

        let mut year = 2000 + remyears + 4 * q_cycles + 100 * c_cycles + 400 * qc_cycles;

        let months = [31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, 29];
        let mut mon = 0;
        for mon_len in months.iter() {
            mon += 1;
            if remdays < *mon_len {
                break;
            }
            remdays -= *mon_len;
        }
        let mday = remdays + 1;
        let mon = if mon + 2 > 12 {
            year += 1;
            mon - 10
        } else {
            mon + 2
        };

        let hours = secs_of_day / 3600;
        let minutes = secs_of_day % 3600 / 60;
        let seconds = secs_of_day % 3600 % 60;

        (
            year as u32,
            mon as u32,
            mday as u32,
            hours as u32,
            minutes as u32,
            seconds as u32,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn level_from_usize_panic() {
        let _crash = Level::from(9);
    }

    #[test]
    fn level_from_usize() {
        for i in 0..=8 {
            let level = Level::from(i);
            assert_eq!(i, level as usize);
        }
    }

    #[test]
    fn level_from_str() {
        assert_eq!(Level::from_str("none"), Ok(Level::None));
        assert_eq!(Level::from_str("NONE"), Ok(Level::None));
        assert_eq!(Level::from_str("none1"), Err(LevelParseError));

        assert_eq!(Level::from_str("emerge"), Ok(Level::Emerge));
        assert_eq!(Level::from_str("EMERGE"), Ok(Level::Emerge));
        assert_eq!(Level::from_str("EMERG2"), Err(LevelParseError));

        assert_eq!(Level::from_str("alert"), Ok(Level::Alert));
        assert_eq!(Level::from_str("ALERT"), Ok(Level::Alert));
        assert_eq!(Level::from_str("ALERT3"), Err(LevelParseError));

        assert_eq!(Level::from_str("critical"), Ok(Level::Critical));
        assert_eq!(Level::from_str("CRITICAL"), Ok(Level::Critical));
        assert_eq!(Level::from_str("crit4"), Err(LevelParseError));

        assert_eq!(Level::from_str("error"), Ok(Level::Error));
        assert_eq!(Level::from_str("Error"), Ok(Level::Error));
        assert_eq!(Level::from_str("5Error5"), Err(LevelParseError));

        assert_eq!(Level::from_str("warning"), Ok(Level::Warning));
        assert_eq!(Level::from_str("WARNING"), Ok(Level::Warning));
        assert_eq!(Level::from_str(" warn"), Err(LevelParseError));

        assert_eq!(Level::from_str("notice"), Ok(Level::Notice));
        assert_eq!(Level::from_str("NoTiCe"), Ok(Level::Notice));
        assert_eq!(Level::from_str("motice"), Err(LevelParseError));

        assert_eq!(Level::from_str("info"), Ok(Level::Info));
        assert_eq!(Level::from_str("INFO"), Ok(Level::Info));
        assert_eq!(Level::from_str("iinfoo"), Err(LevelParseError));

        assert_eq!(Level::from_str("debug"), Ok(Level::Debug));
        assert_eq!(Level::from_str("deBUG"), Ok(Level::Debug));
        assert_eq!(Level::from_str("ddd"), Err(LevelParseError));
    }
}
