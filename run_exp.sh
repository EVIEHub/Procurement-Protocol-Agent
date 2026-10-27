#!/bin/sh
# Use the tools bundled locally for this demo.
set -eu
demo_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
export JAVA_HOME="$demo_dir/.tools/java/Contents/Home"
export PATH="$demo_dir/.tools/node/bin:$JAVA_HOME/bin:$PATH"
export QUINT_HOME="$demo_dir/.quint"
exec python3 "$demo_dir/check.py"
