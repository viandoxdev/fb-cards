import { asset } from '$app/paths';
import type { Card } from '../app';
import type { WorkerRequests, WorkerResponse } from './wasm-worker';
import WasmWorker from './wasm-worker.ts?worker';

export type CardConfig = {
    pageWidth: number;
    fontSize: number;
    useSansFont: boolean;
    textColor: number;
};

let worker: Worker | undefined;
let ready = false;
const outbox: WorkerRequests[] = [];
const pending: ((result: [string, string]) => void)[] = [];

function send(message: WorkerRequests) {
    if (ready) {
        worker?.postMessage(message);
    } else {
        outbox.push(message);
    }
}

function ensureWorker() {
    if (worker || typeof window === 'undefined') return;
    worker = new WasmWorker();
    worker.onerror = (err) => console.error('Card worker error:', err);
    worker.onmessage = (event) => {
        const message = event.data as WorkerResponse;
        if (message.type === 'READY') {
            ready = true;
            worker?.postMessage({
                type: 'INIT',
                payload: { zipUrl: asset('/data-bundle.zip') },
            });
            while (outbox.length) {
                worker?.postMessage(outbox.shift()!);
            }
        } else if (message.type === 'COMPILED_CARD') {
            const resolve = pending.shift();
            if (resolve) resolve(message.payload);
        }
    };
}

if (typeof window !== 'undefined') {
    ensureWorker();
}

export function compileCard(
    card: Card,
    config: CardConfig,
): Promise<[string, string]> {
    ensureWorker();
    return new Promise((resolve) => {
        pending.push(resolve);
        send({ type: 'COMPILE_CARD', payload: { card, config } });
    });
}
