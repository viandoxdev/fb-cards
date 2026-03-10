#!/bin/bash

# This assumes we have fb-cli on hand, and that compile has been ran already.

RUST_LOG=debug ./fb-cli ./ ./public/src/lib/cards.json ./cache/typst/repo ./cache
cd ./cache/typst/
zip -r ../../public/static/data-bundle.zip ./repo ./packages
cd -
