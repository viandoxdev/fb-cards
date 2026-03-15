#!/bin/bash

# This assumes we have fb-cli on hand, and that compile has been ran already.

./fb-cli --search-path ./ --output-file ./public/src/lib/cards.json --output-dir ./cache/typst/repo --exclude ./cache
cd ./cache/typst/
zip -r ../../public/static/data-bundle.zip ./repo ./packages
cd -
