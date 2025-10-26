#!/usr/bin/bash

documents=()

for f in ./*.typ; do
    if ! grep -F -q -e '//![FLASHBANG IGNORE]' -e '//![FLASHBANG INCLUDE]' "$f"; then
        documents+=("$f")
    fi
done

mkdir -p ./dist

for doc in "${documents[@]}"; do
    >&2 echo "compiling $doc"

    base="$(basename -- "$doc")"
    name="${base%.*}"

    typst compile "$doc" "./dist/$name.pdf"
done

cat > ./dist/index.html << EOF
<html>
    <head>
        <title>Flashbang cards</title>
        <meta charset="UTF-8" />
        <style>
            html, body {
                margin: 0;
                padding: 0;
            }

            body {
                display: flex;
                width: 100vw;
                height: 100vh;
                justify-content: center;
                align-items: center;
                flex-direction: column;
                font-size: 2em;
                gap: 1em;
                background: #fafafa;
                font-weight: bold;
            }
            a {
                color: #34abeb;
                text-decoration: none;
            }
        </style>
    </head>
    <body>
        Flashbang cards
EOF

for doc in "${documents[@]}"; do
    base="$(basename -- "$doc")"
    name="${base%.*}"
    echo "<a href=\"$name.pdf\"> $name </a>" >> ./dist/index.html
done

cat >> ./dist/index.html << EOF
    </body>
</html>
EOF
