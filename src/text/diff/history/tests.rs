//! Testing for [`EditHistory`]
//!
//! This module primarily consists of hand-written test cases. These get a little tedious to write,
//! so we have a macro for allowing us to express these a little more nicely. This macro is defined
//! elsewhere, but its syntax has - roughly speaking - the following form:
//! ```ignore
//! test_case! {
//!     fn <test_name>() {
//!         @start <initial string>;
//!         @edit[<edit name>] (<pre-context>)<old edit string>(<post-context>) => <replacement> (<removed>);
//!         @equals <current string>;
//!         @undo <edit name> (<also undone>);
//!         @redo <edit name> (<also redone>);
//!     }
//! }
//! ```
//! Note that `(<pre-context>)`, `(<post-context>)`, and `(<additionally undone>)` are all
//! optional.

use viri_macros::edit_history_test as test_case;

test_case! {
    fn simple_constructive() {
        @start "foo bar baz";
        @edit[A] "bar" => "qux";
        @equals "foo qux baz";
        @edit[B] ("foo")" "("qux") => "";
        @equals "fooqux baz";
        @undo A (B);
        @equals "foo bar baz";
        @redo A (B);
        @equals "fooqux baz";
    }
}

test_case! {
    fn destructive_edit() {
        @start "foo bar baz";

        @edit[A] "bar" => "qux";
        @edit[B] ("q")"u"("x") => "a";
        @equals "foo qax baz";

        @undo A (B);
        @equals "foo bar baz";

        @edit[C] ("bar")" " => "" (A, B);
        @equals "foo barbaz";
    }
}
