"use strict";
/*
 * Support for the Informal Trace Format (ITF):
 * https://apalache-mc.org/docs/adr/015adr-trace.html
 *
 * Igor Konnov, Shon Feder, Informal Systems, 2023
 *
 * Copyright 2021 Informal Systems
 * Licensed under the Apache License, Version 2.0.
 * See LICENSE in the project root for license information.
 */
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.NONDET_PICKS = exports.ACTION_TAKEN = void 0;
exports.toItf = toItf;
exports.ofItf = ofItf;
exports.ofItfNormalized = ofItfNormalized;
exports.ofItfValue = ofItfValue;
exports.pendingDiagnosticsOfItf = pendingDiagnosticsOfItf;
exports.diagnosticsOfItf = diagnosticsOfItf;
const either_1 = require("@sweet-monads/either");
const lodash_1 = require("lodash");
const runtimeValue_1 = __importDefault(require("./runtime/impl/runtimeValue"));
const idGenerator_1 = require("./idGenerator");
exports.ACTION_TAKEN = 'mbt::actionTaken';
exports.NONDET_PICKS = 'mbt::nondetPicks';
// Type predicates to help with type narrowing
function isBigint(v) {
    return v['#bigint'] !== undefined;
}
function isTup(v) {
    return v['#tup'] !== undefined;
}
function isSet(v) {
    return v['#set'] !== undefined;
}
function isMap(v) {
    return v['#map'] !== undefined;
}
function isVariant(v) {
    return (typeof v === 'object' &&
        v !== null &&
        !Array.isArray(v) &&
        Object.keys(v).length === 2 &&
        v['tag'] !== undefined &&
        v['value'] !== undefined);
}
function isUnitVariant(v) {
    return (typeof v === 'object' &&
        v !== null &&
        !Array.isArray(v) &&
        Object.keys(v).length === 1 &&
        v['tag'] !== undefined);
}
function isUnserializable(v) {
    return v['#unserializable'] !== undefined;
}
/**
 * Convert a list of Quint expressions into an object that matches the JSON
 * representation of the ITF trace. This function does not add metadata
 * to the trace. This should be done by the caller.
 *
 * @param vars variable names
 * @param states an array of expressions that represent the states
 * @returns an object that represent the trace in the ITF format
 */
function toItf(vars, states, mbtMetadata = false) {
    const exprToItf = (ex) => {
        switch (ex.kind) {
            case 'int':
                // convert to a special structure, when saving to JSON
                return (0, either_1.right)({ '#bigint': `${ex.value}` });
            case 'str':
            case 'bool':
                return (0, either_1.right)(ex.value);
            case 'app':
                switch (ex.opcode) {
                    case 'List':
                        return (0, either_1.merge)(ex.args.map(exprToItf));
                    case 'Set':
                        return (0, either_1.merge)(ex.args.map(exprToItf)).mapRight(es => {
                            return { '#set': es };
                        });
                    case 'Tup':
                        return (0, either_1.merge)(ex.args.map(exprToItf)).mapRight(es => {
                            return { '#tup': es };
                        });
                    case 'Rec': {
                        if (ex.args.length % 2 !== 0) {
                            return (0, either_1.left)('record: expected an even number of arguments, found:' + ex.args.length);
                        }
                        return (0, either_1.merge)(ex.args.map(exprToItf)).mapRight(kvs => {
                            let obj = {};
                            (0, lodash_1.chunk)(kvs, 2).forEach(([k, v]) => {
                                if (typeof k === 'string') {
                                    obj[k] = v;
                                }
                                else {
                                    (0, either_1.left)(`Invalid record field: ${ex}`);
                                }
                            });
                            return obj;
                        });
                    }
                    case 'Map':
                        return (0, either_1.merge)(
                        // Convert all the entries of the map
                        ex.args.map(exprToItf)).chain(pairs => (0, either_1.merge)(
                        // Quint represents map entries as tuples, but in ITF they are 2 element arrays,
                        // so we unpack all the ITF tuples into arrays
                        pairs.map(p => (isTup(p) ? (0, either_1.right)(p['#tup']) : (0, either_1.left)(`Invalid value in quint Map ${p}`)))).map(entries => 
                        // Finally, we can form the ITF representation of a map
                        ({
                            '#map': entries,
                        })));
                    case 'variant':
                        return (0, either_1.merge)(ex.args.map(exprToItf)).map(([label, value]) => ({ tag: label, value: value }));
                    default:
                        return (0, either_1.left)(`Unexpected operator type: ${ex.opcode}`);
                }
            default:
                return (0, either_1.left)(`Unexpected expression kind: ${ex.kind}`);
        }
    };
    return (0, either_1.merge)(states.map((e, i) => exprToItf(e).chain(obj => typeof obj === 'object'
        ? (0, either_1.right)({ '#meta': { index: i }, ...obj })
        : (0, either_1.left)(`Expected a valid ITF state, but found ${obj}`)))).mapRight(s => {
        if (mbtMetadata) {
            vars = [...vars, exports.ACTION_TAKEN, exports.NONDET_PICKS];
        }
        return {
            vars: vars,
            states: s,
        };
    });
}
function ofItf(itf) {
    // Benign state to synthesize ids for the Quint expressions
    let nextId = 0n;
    // Produce the next ID in sequence
    const getId = () => {
        const id = nextId;
        nextId = nextId + 1n;
        return id;
    };
    return itf.states.map(s => ofItfValue(s, getId));
}
/**
 * Normalizes the given ItfTrace by converting its state to runtime values and
 * back to quint expressions. Note that this round trip results in normalized
 * expression where, for example, maps and sets are sorted alphabetically.
 * Usefull for pretty printing traces produced by Apalache.
 *
 * @param itf - The ItfTrace to normalize
 * @returns An array of its states as normalized quint expressions
 */
function ofItfNormalized(itf) {
    return ofItf(itf).map(runtimeValue_1.default.fromQuintEx).map(runtimeValue_1.default.toQuintEx);
}
function ofItfValue(value, getId) {
    const id = getId();
    if (typeof value === 'boolean') {
        return { id, kind: 'bool', value };
    }
    else if (typeof value === 'string') {
        return { id, kind: 'str', value };
    }
    else if (isBigint(value)) {
        // this is the standard way of encoding an integer in ITF.
        return { id, kind: 'int', value: BigInt(value['#bigint']) };
    }
    else if (typeof value === 'number') {
        // We never encode an integer as a JS number,
        // but we consume it for backwards compatibility with older ITF traces.
        // See: https://apalache-mc.org/docs/adr/015adr-trace.html
        return { id, kind: 'int', value: BigInt(value) };
    }
    else if (Array.isArray(value)) {
        return { id, kind: 'app', opcode: 'List', args: value.map(s => ofItfValue(s, getId)) };
    }
    else if (isTup(value)) {
        return { id, kind: 'app', opcode: 'Tup', args: value['#tup'].map(s => ofItfValue(s, getId)) };
    }
    else if (isSet(value)) {
        return { id, kind: 'app', opcode: 'Set', args: value['#set'].map(s => ofItfValue(s, getId)) };
    }
    else if (isUnserializable(value)) {
        return { id, kind: 'name', name: value['#unserializable'] };
    }
    else if (isMap(value)) {
        const args = value['#map'].map(([key, value]) => {
            const k = ofItfValue(key, getId);
            const v = ofItfValue(value, getId);
            return { id: getId(), kind: 'app', opcode: 'Tup', args: [k, v] };
        });
        return {
            id,
            kind: 'app',
            opcode: 'Map',
            args,
        };
    }
    else if (isUnitVariant(value)) {
        const l = ofItfValue(value.tag, getId);
        if (l.kind === 'str' && l.value === 'UNIT') {
            // Apalache converts empty tuples to its unit value, { tag: "UNIT" }.
            // We need to convert it back to Quint's unit value, the empty tuple.
            return { id, kind: 'app', opcode: 'Tup', args: [] };
        }
        return {
            id,
            kind: 'app',
            opcode: 'Rec',
            args: [{ id: getId(), kind: 'str', value: 'tag' }, l],
        };
    }
    else if (isVariant(value)) {
        const l = ofItfValue(value.tag, getId);
        const v = ofItfValue(value.value, getId);
        return { id, kind: 'app', opcode: 'variant', args: [l, v] };
    }
    else if (typeof value === 'object') {
        // Any other object must represent a record
        // For each key/value pair in the object, form the quint expressions representing
        // the record field and value
        const args = Object.keys(value)
            .filter(key => key !== '#meta' && !key.startsWith('__')) // Must be removed from top-level objects representing states
            .map(f => [{ id: getId(), kind: 'str', value: f }, ofItfValue(value[f], getId)])
            .flat(); // flatten the converted pairs of fields into a single array
        return { id, kind: 'app', opcode: 'Rec', args };
    }
    else {
        // This should be impossible, but TypeScript can't tell we've handled all cases
        throw new Error(`internal error: unhandled ITF value ${value}`);
    }
}
/** Extracts pending diagnostics from the ITF trace-level metadata.
 * These are diagnostics from a failing step that never produced a new state. */
function pendingDiagnosticsOfItf(itf) {
    if (itf['#meta']?.pending_diagnostics) {
        const msgs = JSON.parse(itf['#meta'].pending_diagnostics);
        msgs.forEach(msg => (msg.value = ofItfValue(msg.value, idGenerator_1.zerog.nextId)));
        return msgs;
    }
    return [];
}
/** Extracts diagnostics embedded into ITF's metadata. Returns a matrics of
 * diagnostics per state in the ITF trace. */
function diagnosticsOfItf(itf) {
    var diagnostics = [];
    for (const state of itf.states) {
        if ('#meta' in state && 'diagnostics' in state['#meta']) {
            const msgs = JSON.parse(state['#meta'].diagnostics);
            msgs.forEach(msg => (msg.value = ofItfValue(msg.value, idGenerator_1.zerog.nextId)));
            diagnostics.push(msgs);
        }
    }
    return diagnostics;
}
//# sourceMappingURL=itf.js.map