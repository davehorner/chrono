// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The local (system) time zone.

#[cfg(any(unix, windows))]
use std::cmp::Ordering;

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use super::fixed::FixedOffset;
use super::{LocalResult, TimeZone};
use crate::{DateTime, NaiveDateTime, Utc};

#[cfg(unix)]
#[path = "unix.rs"]
mod inner;

#[cfg(windows)]
#[path = "windows.rs"]
mod inner;

#[cfg(all(windows, feature = "clock"))]
#[allow(unreachable_pub)]
mod win_bindings;

#[cfg(all(
    not(unix),
    not(windows),
    not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))
))]
mod inner {
    use crate::{FixedOffset, LocalResult, NaiveDateTime};

    pub(super) fn offset_from_utc_datetime(_utc_time: &NaiveDateTime) -> LocalResult<FixedOffset> {
        LocalResult::Single(FixedOffset::east_opt(0).unwrap())
    }

    pub(super) fn offset_from_local_datetime(
        _local_time: &NaiveDateTime,
    ) -> LocalResult<FixedOffset> {
        LocalResult::Single(FixedOffset::east_opt(0).unwrap())
    }
}

#[cfg(all(
    target_arch = "wasm32",
    feature = "wasmbind",
    not(any(target_os = "emscripten", target_os = "wasi"))
))]
mod inner {
    use crate::{Datelike, FixedOffset, LocalResult, NaiveDateTime, Timelike};

    pub(super) fn offset_from_utc_datetime(utc: &NaiveDateTime) -> LocalResult<FixedOffset> {
        let offset = js_sys::Date::from(utc.and_utc()).get_timezone_offset();
        LocalResult::Single(FixedOffset::west_opt((offset as i32) * 60).unwrap())
    }

    pub(super) fn offset_from_local_datetime(local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        let mut year = local.year();
        if year < 100 {
            // The API in `js_sys` does not let us create a `Date` with negative years.
            // And values for years from `0` to `99` map to the years `1900` to `1999`.
            // Shift the value by a multiple of 400 years until it is `>= 100`.
            let shift_cycles = (year - 100).div_euclid(400);
            year -= shift_cycles * 400;
        }
        let js_date = js_sys::Date::new_with_year_month_day_hr_min_sec(
            year as u32,
            local.month0() as i32,
            local.day() as i32,
            local.hour() as i32,
            local.minute() as i32,
            local.second() as i32,
            // ignore milliseconds, our representation of leap seconds may be problematic
        );
        let offset = js_date.get_timezone_offset();
        // We always get a result, even if this time does not exist or is ambiguous.
        LocalResult::Single(FixedOffset::west_opt((offset as i32) * 60).unwrap())
    }
}

#[cfg(unix)]
mod tz_info;

/// The local timescale. This is implemented via the standard `time` crate.
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on the Local struct is the preferred way to construct `DateTime<Local>`
/// instances.
///
/// # Example
///
/// ```
/// use chrono::{Local, DateTime, TimeZone};
///
/// let dt1: DateTime<Local> = Local::now();
/// let dt2: DateTime<Local> = Local.timestamp_opt(0, 0).unwrap();
/// assert!(dt1 >= dt2);
/// ```
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
#[cfg_attr(feature = "rkyv", archive_attr(derive(Clone, Copy, Debug)))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Local;

impl Local {
    /// Returns a `DateTime<Local>` which corresponds to the current date, time and offset from
    /// UTC.
    ///
    /// See also the similar [`Utc::now()`] which returns `DateTime<Utc>`, i.e. without the local
    /// offset.
    ///
    /// # Example
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// # use chrono::{DateTime, FixedOffset, Local};
    /// // Current local time
    /// let now = Local::now();
    ///
    /// // Current local date
    /// let today = now.date_naive();
    ///
    /// // Current local time, converted to `DateTime<FixedOffset>`
    /// let now_fixed_offset = Local::now().fixed_offset();
    /// // or
    /// let now_fixed_offset: DateTime<FixedOffset> = Local::now().into();
    ///
    /// // Current time in some timezone (let's use +05:00)
    /// // Note that it is usually more efficient to use `Utc::now` for this use case.
    /// let offset = FixedOffset::east_opt(5 * 60 * 60).unwrap();
    /// let now_with_offset = Local::now().with_timezone(&offset);
    /// ```
    pub fn now() -> DateTime<Local> {
        Utc::now().with_timezone(&Local)
    }
}

impl TimeZone for Local {
    type Offset = FixedOffset;

    fn from_offset(_offset: &FixedOffset) -> Local {
        Local
    }

    fn offset_from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        inner::offset_from_local_datetime(local)
    }

    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> FixedOffset {
        inner::offset_from_utc_datetime(utc).unwrap()
    }
}

#[cfg(any(unix, windows))]
#[derive(Copy, Clone, Eq, PartialEq)]
struct Transition {
    transition_utc: NaiveDateTime,
    offset_before: FixedOffset,
    offset_after: FixedOffset,
}

#[cfg(any(unix, windows))]
impl Transition {
    fn new(
        transition_local: NaiveDateTime,
        offset_before: FixedOffset,
        offset_after: FixedOffset,
    ) -> Transition {
        // FIXME: adding or substracting an offset can overflow if the transition date is very
        // close to `NaiveDate::MIN` or `NaiveDate::MAX`.
        Transition { transition_utc: transition_local - offset_before, offset_before, offset_after }
    }

    // Depending on the dst and std offsets, the result of a transition can have a local time that
    // is before or after the start of the transition.
    //
    // We are interested in the earliest and latest local clock time of the transition, as this are
    // the times between which times do not exist or are ambiguous.
    fn transition_min_max(&self) -> (NaiveDateTime, NaiveDateTime) {
        // FIXME: adding or substracting an offset can overflow if the transition date is very
        // close to `NaiveDate::MIN` or `NaiveDate::MAX`.
        if self.offset_after.local_minus_utc() > self.offset_before.local_minus_utc() {
            (self.transition_utc + self.offset_before, self.transition_utc + self.offset_after)
        } else {
            (self.transition_utc + self.offset_after, self.transition_utc + self.offset_before)
        }
    }
}

#[cfg(any(unix, windows))]
impl PartialOrd for Transition {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.transition_utc.cmp(&other.transition_utc))
    }
}

#[cfg(any(unix, windows))]
impl Ord for Transition {
    fn cmp(&self, other: &Self) -> Ordering {
        self.transition_utc.cmp(&other.transition_utc)
    }
}

// Calculate the time in UTC given a local time, and transitions.
// `transitions` must be sorted.
#[cfg(any(unix, windows))]
fn lookup_with_dst_transitions(
    transitions: &[Transition],
    dt: NaiveDateTime,
) -> LocalResult<FixedOffset> {
    for t in transitions.iter() {
        let (transition_min, transition_max) = t.transition_min_max();
        if dt < transition_min {
            return LocalResult::Single(t.offset_before);
        } else if dt <= transition_max {
            return match t.offset_after.local_minus_utc().cmp(&t.offset_before.local_minus_utc()) {
                Ordering::Equal => LocalResult::Single(t.offset_before),
                Ordering::Less => LocalResult::Ambiguous(t.offset_before, t.offset_after),
                Ordering::Greater => {
                    if dt == transition_min {
                        LocalResult::Single(t.offset_before)
                    } else if dt == transition_max {
                        LocalResult::Single(t.offset_after)
                    } else {
                        LocalResult::None
                    }
                }
            };
        }
    }
    LocalResult::Single(transitions.last().unwrap().offset_after)
}

#[cfg(test)]
mod tests {
    use super::Local;
    #[cfg(any(unix, windows))]
    use crate::offset::local::{lookup_with_dst_transitions, Transition};
    use crate::offset::TimeZone;
    use crate::{Datelike, Duration, Utc};
    #[cfg(any(unix, windows))]
    use crate::{FixedOffset, LocalResult, NaiveDate};

    #[test]
    fn verify_correct_offsets() {
        let now = Local::now();
        let from_local = Local.from_local_datetime(&now.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&now.naive_utc());

        assert_eq!(now.offset().local_minus_utc(), from_local.offset().local_minus_utc());
        assert_eq!(now.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(now, from_local);
        assert_eq!(now, from_utc);
    }

    #[test]
    fn verify_correct_offsets_distant_past() {
        // let distant_past = Local::now() - Duration::days(365 * 100);
        let distant_past = Local::now() - Duration::days(365 * 500);
        let from_local = Local.from_local_datetime(&distant_past.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&distant_past.naive_utc());

        assert_eq!(distant_past.offset().local_minus_utc(), from_local.offset().local_minus_utc());
        assert_eq!(distant_past.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(distant_past, from_local);
        assert_eq!(distant_past, from_utc);
    }

    #[test]
    fn verify_correct_offsets_distant_future() {
        let distant_future = Local::now() + Duration::days(365 * 35000);
        let from_local = Local.from_local_datetime(&distant_future.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&distant_future.naive_utc());

        assert_eq!(
            distant_future.offset().local_minus_utc(),
            from_local.offset().local_minus_utc()
        );
        assert_eq!(distant_future.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(distant_future, from_local);
        assert_eq!(distant_future, from_utc);
    }

    #[test]
    fn test_local_date_sanity_check() {
        // issue #27
        assert_eq!(Local.with_ymd_and_hms(2999, 12, 28, 0, 0, 0).unwrap().day(), 28);
    }

    #[test]
    fn test_leap_second() {
        // issue #123
        let today = Utc::now().date_naive();

        if let Some(dt) = today.and_hms_milli_opt(15, 2, 59, 1000) {
            let timestr = dt.time().to_string();
            // the OS API may or may not support the leap second,
            // but there are only two sensible options.
            assert!(
                timestr == "15:02:60" || timestr == "15:03:00",
                "unexpected timestr {:?}",
                timestr
            );
        }

        if let Some(dt) = today.and_hms_milli_opt(15, 2, 3, 1234) {
            let timestr = dt.time().to_string();
            assert!(
                timestr == "15:02:03.234" || timestr == "15:02:04.234",
                "unexpected timestr {:?}",
                timestr
            );
        }
    }

    #[test]
    #[cfg(any(unix, windows))]
    fn test_lookup_with_dst_transitions() {
        let ymdhms = |y, m, d, h, n, s| {
            NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap()
        };

        #[track_caller]
        #[allow(clippy::too_many_arguments)]
        fn compare_lookup(
            transitions: &[Transition],
            y: i32,
            m: u32,
            d: u32,
            h: u32,
            n: u32,
            s: u32,
            result: LocalResult<FixedOffset>,
        ) {
            let dt = NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap();
            assert_eq!(lookup_with_dst_transitions(transitions, dt), result);
        }

        // dst transition before std transition
        // dst offset > std offset
        let std = FixedOffset::east_opt(3 * 60 * 60).unwrap();
        let dst = FixedOffset::east_opt(4 * 60 * 60).unwrap();
        let transitions = [
            Transition::new(ymdhms(2023, 3, 26, 2, 0, 0), std, dst),
            Transition::new(ymdhms(2023, 10, 29, 3, 0, 0), dst, std),
        ];
        compare_lookup(&transitions, 2023, 3, 26, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 3, 26, 2, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 3, 26, 2, 30, 0, LocalResult::None);
        compare_lookup(&transitions, 2023, 3, 26, 3, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 3, 26, 4, 0, 0, LocalResult::Single(dst));

        compare_lookup(&transitions, 2023, 10, 29, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 10, 29, 2, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 10, 29, 2, 30, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 10, 29, 3, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 10, 29, 4, 0, 0, LocalResult::Single(std));

        // std transition before dst transition
        // dst offset > std offset
        let std = FixedOffset::east_opt(-5 * 60 * 60).unwrap();
        let dst = FixedOffset::east_opt(-4 * 60 * 60).unwrap();
        let transitions = [
            Transition::new(ymdhms(2023, 3, 24, 3, 0, 0), dst, std),
            Transition::new(ymdhms(2023, 10, 27, 2, 0, 0), std, dst),
        ];
        compare_lookup(&transitions, 2023, 3, 24, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 3, 24, 2, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 3, 24, 2, 30, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 3, 24, 3, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 3, 24, 4, 0, 0, LocalResult::Single(std));

        compare_lookup(&transitions, 2023, 10, 27, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 10, 27, 2, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 10, 27, 2, 30, 0, LocalResult::None);
        compare_lookup(&transitions, 2023, 10, 27, 3, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 10, 27, 4, 0, 0, LocalResult::Single(dst));

        // dst transition before std transition
        // dst offset < std offset
        let std = FixedOffset::east_opt(3 * 60 * 60).unwrap();
        let dst = FixedOffset::east_opt((2 * 60 + 30) * 60).unwrap();
        let transitions = [
            Transition::new(ymdhms(2023, 3, 26, 2, 30, 0), std, dst),
            Transition::new(ymdhms(2023, 10, 29, 2, 0, 0), dst, std),
        ];
        compare_lookup(&transitions, 2023, 3, 26, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 3, 26, 2, 0, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 3, 26, 2, 15, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 3, 26, 2, 30, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 3, 26, 3, 0, 0, LocalResult::Single(dst));

        compare_lookup(&transitions, 2023, 10, 29, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 10, 29, 2, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 10, 29, 2, 15, 0, LocalResult::None);
        compare_lookup(&transitions, 2023, 10, 29, 2, 30, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 10, 29, 3, 0, 0, LocalResult::Single(std));

        // std transition before dst transition
        // dst offset < std offset
        let std = FixedOffset::east_opt(-(4 * 60 + 30) * 60).unwrap();
        let dst = FixedOffset::east_opt(-5 * 60 * 60).unwrap();
        let transitions = [
            Transition::new(ymdhms(2023, 3, 24, 2, 0, 0), dst, std),
            Transition::new(ymdhms(2023, 10, 27, 2, 30, 0), std, dst),
        ];
        compare_lookup(&transitions, 2023, 3, 24, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 3, 24, 2, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 3, 24, 2, 15, 0, LocalResult::None);
        compare_lookup(&transitions, 2023, 3, 24, 2, 30, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 3, 24, 3, 0, 0, LocalResult::Single(std));

        compare_lookup(&transitions, 2023, 10, 27, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 10, 27, 2, 0, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 10, 27, 2, 15, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 10, 27, 2, 30, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 10, 27, 3, 0, 0, LocalResult::Single(dst));

        // offset stays the same
        let std = FixedOffset::east_opt(3 * 60 * 60).unwrap();
        let transitions = [
            Transition::new(ymdhms(2023, 3, 26, 2, 0, 0), std, std),
            Transition::new(ymdhms(2023, 10, 29, 3, 0, 0), std, std),
        ];
        compare_lookup(&transitions, 2023, 3, 26, 2, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 10, 29, 3, 0, 0, LocalResult::Single(std));
    }

    /// Test Issue #866
    #[test]
    fn test_issue_866() {
        #[allow(deprecated)]
        let local_20221106 = Local.ymd(2022, 11, 6);
        let _dt_20221106 = local_20221106.and_hms_milli_opt(1, 2, 59, 1000).unwrap();
    }
}
