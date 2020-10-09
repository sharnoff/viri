use chrono::format::Item as TimeFormatItem;
use chrono::prelude::{DateTime, Local};
use serde::{Deserialize, Serialize, Serializer};
use std::convert::TryFrom;
use std::fmt::{self, Debug, Formatter};

#[derive(Clone, Deserialize)]
#[serde(try_from = "String")]
pub(super) struct TimeFormat {
    items: Vec<TimeFormatItem<'static>>,
    string: String,
}

impl TimeFormat {
    pub fn now(&self) -> String {
        let current_time: DateTime<Local> = Local::now();
        current_time
            .format_with_items(self.items.iter())
            .to_string()
    }
}

impl Serialize for TimeFormat {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.string)
    }
}

impl TryFrom<String> for TimeFormat {
    type Error = &'static str;

    fn try_from(string: String) -> Result<TimeFormat, &'static str> {
        use chrono::format::{Item, StrftimeItems};

        let mut items = Vec::new();
        for item in StrftimeItems::new(&string) {
            let new_item = match item {
                Item::Error => return Err("invalid time format string"),
                Item::Literal(s) => Item::OwnedLiteral(Box::from(s)),
                Item::OwnedLiteral(s) => Item::OwnedLiteral(s),
                Item::Space(s) => Item::OwnedSpace(Box::from(s)),
                Item::OwnedSpace(s) => Item::OwnedSpace(s),
                Item::Numeric(n, p) => Item::Numeric(n, p),
                Item::Fixed(f) => Item::Fixed(f),
            };

            items.push(new_item);
        }

        Ok(TimeFormat { items, string })
    }
}

impl Debug for TimeFormat {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.string.fmt(f)
    }
}
