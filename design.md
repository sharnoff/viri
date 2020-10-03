# The high-level design of the editor

This document hopes to serve as a high-level guide to the internal workings of the editor -
primarily looking at the interactions between the different components, and how they come together
to produce the full application.

### Table of contents

* [A few words on async](#a-few-words-on-async)
* [The fundamental pieces](#the-fundamental-pieces)
  * [Datatypes](#datatypes)
  * [Processes](#processes)

### A few words on async

The fundamental building block of the editor's functioning is through async Rust and futures. This
is a practical necessity, because there are so many different interacting pieces that spinning up a
new OS-thread for each task is irresponsible.

For example: We use a couple distinct tasks are responsible for receiving events (both through the
terminal, and via signals), rendering different splits can be split and executed in parallel, and
syntax highlighting is done entirely as its own task!

If we hadn't made this sort of separation, we would have been forced to either:
  (a) do highlighting every time we want to draw the screen, or
  (b) use a separate thread to handle highlighting (which is a slippery slope itself)

So asynchronous programming it is. Aside from technical constraints, writing this in an asynchronous
fashion just makes it all simpler!

## The fundamental pieces

There are essentially two ways that we can look at the way that functionality is built up: through
the types that store the relevant data, and through the processes that action on them. In some caes,
these are linked - like with `View`s that have their own channels to listen on for events. But it's
generally helpful for us to consider these as separate.

### Datatypes

The simpler of the two categories to look at are the big, persistent types we use.

At the highest level, we have each individual `View` - these are arranged into a tree, where each
individual `View` represents a region of the screen. In practice, we're much more interested in the
*leaves* of this tree, which form the interactive splits in the editor. The parent nodes in the tree
are the wrappers giving horizontal and veritical splits.

There's some more information about this given in the dedicated [submodule](src/views/split.rs) for
horizontal and veritcal splits.

As part of each view into a file, we also have the `Lines` struct, which is used for managing the
low-level interactions with text. It's shared between views into the file, and stores the underlying
bytes representing the file. Because of this, it is also responsible for storing styling
information, which is how we do syntax highlighting.

### Processes

TODO
