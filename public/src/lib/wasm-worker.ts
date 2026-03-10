import type { Card } from '../app';
import { Card as FBCard, Core, SourceConfig } from '../fb-web';

// 1. Declare the core variable and wrap the async setup in a Promise
let core: Core;
const initPromise = (async () => {
    const response = await fetch("data-bundle.zip");
    const buffer = await response.arrayBuffer();
    core = new Core(new Uint8Array(buffer));
})();

export type WorkerRequests =
    | { type: "COMPILE_CARD", payload: { card: Card, config: { pageWidth: number, useSansFont: boolean, fontSize: number, textColor: number } } };

export type WorkerResponse =
    | { type: "COMPILED_CARD", payload: [string, string] };

self.onmessage = async (event) => {
    await initPromise;

    const message = event.data as WorkerRequests;

    switch (message.type) {
        case 'COMPILE_CARD':
            const card = message.payload.card;
            core.prepare_source(
                [new FBCard(card.header, card.id, card.name, card.question, card.answer, card.locations)], 
                new SourceConfig(message.payload.config.pageWidth, message.payload.config.fontSize, message.payload.config.textColor, message.payload.config.useSansFont)
            );
            const pages = core.compile();
            let svgs = [pages[1].svg(), pages[2].svg()];
            self.postMessage({ type: "COMPILED_CARD", payload: svgs });
            break;
    }
}
