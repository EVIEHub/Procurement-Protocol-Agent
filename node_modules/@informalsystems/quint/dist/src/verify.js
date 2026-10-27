"use strict";
/* ----------------------------------------------------------------------------------
 * Copyright 2025 Informal Systems
 * Licensed under the Apache License, Version 2.0.
 * See LICENSE in the project root for license information.
 * --------------------------------------------------------------------------------- */
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.verifyWithTlcBackend = verifyWithTlcBackend;
exports.verifyWithApalacheBackend = verifyWithApalacheBackend;
/**
 * Core verification functionality
 *
 * @author Yassine Boukhari, 2025
 *
 * @module
 */
const chalk_1 = __importDefault(require("chalk"));
const apalache_1 = require("./apalache");
const tlc_1 = require("./tlc");
const compileToTlaplus_1 = require("./compileToTlaplus");
const initToPredicate_1 = require("./ir/initToPredicate");
const cliReporting_1 = require("./cliReporting");
const cliHelpers_1 = require("./cliHelpers");
const verbosity_1 = require("./verbosity");
const either_1 = require("@sweet-monads/either");
// --------------------------------------------------------------------------------
// TLC
// --------------------------------------------------------------------------------
async function verifyWithTlcBackend(prev, verifying, verbosityLevel) {
    const args = prev.args;
    const removeRuns = (module) => {
        return { ...module, declarations: module.declarations.filter(d => d.kind !== 'def' || d.qualifier !== 'run') };
    };
    const mainModule = (0, initToPredicate_1.convertInit)(removeRuns(prev.mainModule), prev.table, prev.modes);
    if (mainModule.isLeft()) {
        return (0, cliReporting_1.cliErr)('Failed to convert init to predicate', {
            ...verifying,
            errors: mainModule.value.map((0, cliHelpers_1.mkErrorMessage)(prev.sourceMap)),
        });
    }
    const verifyingFlat = { ...prev, modules: [mainModule.value] };
    const parsedSpec = (0, cliReporting_1.outputJson)(verifyingFlat);
    if (verbosity_1.verbosity.hasProgress(verbosityLevel)) {
        console.log(chalk_1.default.green('[TLC]') + ' Compiling to TLA+ (via Apalache)...');
    }
    const tlaResult = await (0, compileToTlaplus_1.compileToTlaplus)(args.serverEndpoint, args.apalacheVersion, parsedSpec, verbosityLevel);
    if (tlaResult.isLeft()) {
        return (0, cliReporting_1.cliErr)('error', { ...verifying, errors: tlaResult.value.errors });
    }
    const [, invariantsList] = (0, cliHelpers_1.getInvariants)(args);
    const tlcRuntimeConfig = (0, tlc_1.loadTlcConfig)(args.tlcConfig);
    // Ensure the Apalache distribution is available locally (TLC needs the JAR)
    const distResult = await (0, apalache_1.fetchApalache)(args.apalacheVersion, verbosityLevel);
    if (distResult.isLeft()) {
        return (0, cliReporting_1.cliErr)('error', { ...verifying, errors: distResult.value.errors });
    }
    if (verbosity_1.verbosity.hasProgress(verbosityLevel)) {
        console.log(chalk_1.default.green('[TLC]') + ' Running TLC model checker...\n');
    }
    const startMs = Date.now();
    const tlcResult = await (0, tlc_1.verify)({
        tlaCode: tlaResult.value,
        moduleName: prev.main,
        hasInvariant: invariantsList.length > 0,
        hasTemporal: !!args.temporal,
    }, args.apalacheVersion, tlcRuntimeConfig, verbosityLevel);
    return (0, cliReporting_1.processTlcResult)(tlcResult, startMs, verbosityLevel, verifying);
}
// --------------------------------------------------------------------------------
// Apalache
// --------------------------------------------------------------------------------
/**
 * Verifies the configuration `config` by model checking it with the Apalache server
 *
 * @param serverEndpoint
 *   a server endpoint
 *
 * @param config
 *   an apalache configuration. See https://github.com/apalache-mc/apalache/blob/main/mod-infra/src/main/scala/at/forsyte/apalache/infra/passes/options.scala#L255
 *
 * @returns right(void) if verification succeeds, or left(err) explaining the failure
 */
async function verifyWithApalache(serverEndpoint, apalacheVersion, config, verbosityLevel) {
    const connectionResult = await (0, apalache_1.connect)(serverEndpoint, apalacheVersion, verbosityLevel);
    return connectionResult.asyncChain(conn => conn.check(config));
}
async function verifyWithApalacheBackend(prev, verifying, verbosityLevel) {
    const args = prev.args;
    const itfFile = prev.args.outItf;
    if (itfFile) {
        if (itfFile.includes(cliHelpers_1.PLACEHOLDERS.test) || itfFile.includes(cliHelpers_1.PLACEHOLDERS.seq)) {
            console.log(`${chalk_1.default.yellow('[warning]')} the output file contains ${chalk_1.default.grey(cliHelpers_1.PLACEHOLDERS.test)} or ${chalk_1.default.grey(cliHelpers_1.PLACEHOLDERS.seq)}, but this has no effect since at most a single trace will be produced.`);
        }
    }
    const loadedConfig = (0, cliHelpers_1.loadApalacheConfig)(prev, args.apalacheConfig);
    const verifyingFlat = { ...prev, modules: [prev.mainModule] };
    const parsedSpec = (0, cliReporting_1.outputJson)(verifyingFlat);
    const [invariantsString, invariantsList] = (0, cliHelpers_1.getInvariants)(prev.args);
    // Parse individual invariants into QuintEx for Rust-based violation reporting.
    let invariantExprs;
    if (invariantsList.length > 1 || (invariantsList.length > 0 && args.inductiveInvariant)) {
        const parsed = (0, either_1.mergeInMany)(invariantsList.map(inv => (0, cliHelpers_1.toExpr)(prev, inv)));
        if (parsed.isRight()) {
            invariantExprs = parsed.value;
        }
    }
    if (args.inductiveInvariant) {
        const hasOrdinaryInvariant = invariantsList.length > 0;
        const nPhases = hasOrdinaryInvariant ? 3 : 2;
        const initConfig = (0, apalache_1.createConfig)(loadedConfig, parsedSpec, { ...args, maxSteps: 0 }, ['q::inductiveInv']);
        // Checking whether the inductive invariant holds in the initial state(s)
        (0, cliReporting_1.printInductiveInvariantProgress)(verbosityLevel, args, 1, nPhases);
        const startMs = Date.now();
        return verifyWithApalache(args.serverEndpoint, args.apalacheVersion, initConfig, verbosityLevel).then(async (res) => {
            if (res.isLeft()) {
                return (0, cliReporting_1.processApalacheResult)(res, startMs, verbosityLevel, verifying, [args.inductiveInvariant]);
            }
            // Checking whether the inductive invariant is preserved by the step
            (0, cliReporting_1.printInductiveInvariantProgress)(verbosityLevel, args, 2, nPhases);
            const stepConfig = (0, apalache_1.createConfig)(loadedConfig, parsedSpec, { ...args, maxSteps: 1 }, ['q::inductiveInv'], 'q::inductiveInv');
            return verifyWithApalache(args.serverEndpoint, args.apalacheVersion, stepConfig, verbosityLevel).then(async (res) => {
                if (res.isLeft() || !hasOrdinaryInvariant) {
                    return (0, cliReporting_1.processApalacheResult)(res, startMs, verbosityLevel, verifying, [args.inductiveInvariant]);
                }
                // Checking whether the inductive invariant implies the ordinary invariant
                (0, cliReporting_1.printInductiveInvariantProgress)(verbosityLevel, args, 3, nPhases, invariantsString);
                const propConfig = (0, apalache_1.createConfig)(loadedConfig, parsedSpec, { ...args, maxSteps: 0 }, ['q::inv'], 'q::inductiveInv');
                return verifyWithApalache(args.serverEndpoint, args.apalacheVersion, propConfig, verbosityLevel).then(async (res) => {
                    return (0, cliReporting_1.processApalacheResult)(res, startMs, verbosityLevel, verifying, invariantsList, invariantExprs, prev.resolver.table);
                });
            });
        });
    }
    // We need to insert the data from CLI args into their appropriate locations
    // in the Apalache config
    const config = (0, apalache_1.createConfig)(loadedConfig, parsedSpec, args, invariantsList.length > 0 ? ['q::inv'] : []);
    const startMs = Date.now();
    return verifyWithApalache(args.serverEndpoint, args.apalacheVersion, config, verbosityLevel).then(async (res) => {
        return (0, cliReporting_1.processApalacheResult)(res, startMs, verbosityLevel, verifying, invariantsList, invariantExprs, prev.resolver.table);
    });
}
//# sourceMappingURL=verify.js.map