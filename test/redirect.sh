#!/bin/sh

echo "Setting up testing environment..."

mkfifo stdin 2> /dev/null && echo "Created stdin pipe at '$(pwd)/stdin'" || echo "Stdin already exists at '$(pwd)/stdin'"
mkfifo stdout 2> /dev/null && echo "Created stdout pipe at '$(pwd)/stdout'" || echo "Stdin already exists at '$(pwd)/stdout'"
mkfifo stderr 2> /dev/null && echo "Created stderr pipe at '$(pwd)/stderr'" || echo "Stderr already exists at '$(pwd)/stderr'"

echo "Testing..."
echo "=============="

cargo run -- -l log --log-level=Trace "$@" < stdin > stdout 2> stderr
