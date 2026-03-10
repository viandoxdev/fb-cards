import type { Card } from '../app';
import { Card as FBCard, Core, SourceConfig } from '../fb-web';

let core: Core;
let resolveInit: () => void;

// 1. Create a promise that resolves ONLY when we call resolveInit()
const initPromise = new Promise<void>((resolve) => {
    resolveInit = resolve;
});

export type WorkerRequests =
    | { type: "INIT", payload: { zipUrl: string } }
    | { type: "COMPILE_CARD", payload: { card: Card, config: { pageWidth: number, useSansFont: boolean, fontSize: number, textColor: number } } };

export type WorkerResponse =
    | { type: "COMPILED_CARD", payload: [string, string] }
    | { type: "READY", payload: null };

self.onmessage = async (event) => {
    const message = event.data as WorkerRequests;

    if (message.type === 'INIT') {
        console.log("Received wasm-bundle url !", message.payload.zipUrl);
        // 2. Fetch using the URL provided by the main thread
        const response = await fetch(message.payload.zipUrl);
        const buffer = await response.arrayBuffer();
        core = new Core(new Uint8Array(buffer));

        console.log("Core initialized.");
        // 3. Unlock the queue!
        resolveInit();
        return; // Don't process further for the INIT message
    }

    // 4. Any COMPILE_CARD messages will pause here until INIT is done
    await initPromise;

    if (message.type === 'COMPILE_CARD') {
        const card = message.payload.card;
        core.prepare_source(
            [new FBCard(card.header, card.id, card.name, card.question, card.answer, card.locations)],
            new SourceConfig(message.payload.config.pageWidth, message.payload.config.fontSize, message.payload.config.textColor, message.payload.config.useSansFont)
        );
        const pages = core.compile();
        self.postMessage({ type: "COMPILED_CARD", payload: [pages[1].svg(), pages[2].svg()] });
    }
}

self.postMessage({ type: "READY", payload: null })
