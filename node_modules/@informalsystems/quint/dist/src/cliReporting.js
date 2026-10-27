"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.maybePrintCounterExample = maybePrintCounterExample;
exports.maybePrintWitnesses = maybePrintWitnesses;
exports.printViolatedInvariantsByIndex = printViolatedInvariantsByIndex;
exports.printViolatedInvariants = printViolatedInvariants;
exports.processTlcResult = processTlcResult;
exports.processApalacheResult = processApalacheResult;
exports.outputJson = outputJson;
exports.writeOutputToJson = writeOutputToJson;
exports.jsonStringOfOutputStage = jsonStringOfOutputStage;
exports.writeToJson = writeToJson;
exports.cliErr = cliErr;
exports.findMainModule = findMainModule;
exports.handleMainModuleError = handleMainModuleError;
exports.prepareOnTrace = prepareOnTrace;
exports.outputTestResults = outputTestResults;
exports.outputTestErrors = outputTestErrors;
exports.printInductiveInvariantProgress = printInductiveInvariantProgress;
const chalk_1 = __importDefault(require("chalk"));
const graphics_1 = require("./graphics");
const verbosity_1 = require("./verbosity");
const trace_1 = require("./runtime/trace");
const json_bigint_1 = __importDefault(require("json-bigint"));
const evaluator_1 = require("./runtime/impl/evaluator");
const rng_1 = require("./rng");
const fs_1 = require("fs");
const path_1 = require("path");
const itf_1 = require("./itf");
const cliHelpers_1 = require("./cliHelpers");
const either_1 = require("@sweet-monads/either");
const process_1 = require("process");
const jsonHelper_1 = require("./jsonHelper");
const invariantsReporter_1 = require("./rust/invariantsReporter");
const errorReporter_1 = require("./errorReporter");
const prettierimp_1 = require("./prettierimp");
/**
 * Print a counterexample if the appropriate verbosity is set.
 *
 * @param verbosityLevel The verbosity level.
 * @param states The states of the counterexample.
 * @param frames The execution frames (optional).
 * @param hideVars Variables to hide in the output (optional).
 */
function maybePrintCounterExample(verbosityLevel, states, diagnostics, frames = [], hideVars = [], pendingDiagnostics) {
    if (verbosity_1.verbosity.hasStateOutput(verbosityLevel)) {
        console.log(chalk_1.default.gray('An example execution:\n'));
        const myConsole = {
            width: (0, graphics_1.terminalWidth)(),
            out: (s) => process.stdout.write(s),
        };
        (0, graphics_1.printTrace)(myConsole, states, diagnostics, frames, hideVars, pendingDiagnostics);
    }
}
/**
 * Print witnesses if the appropriate verbosity is set.
 *
 * @param verbosityLevel The verbosity level.
 * @param outcome The simulation outcome.
 * @param witnesses The list of witnesses.
 */
function maybePrintWitnesses(verbosityLevel, outcome, witnesses) {
    if (verbosity_1.verbosity.hasWitnessesOutput(verbosityLevel)) {
        if (outcome.witnessingTraces.length > 0) {
            console.log(chalk_1.default.green('Witnesses:'));
        }
        outcome.witnessingTraces.forEach((n, i) => {
            const percentage = chalk_1.default.gray(`(${(((1.0 * n) / outcome.samples) * 100).toFixed(2)}%)`);
            console.log(`${chalk_1.default.yellow(witnesses[i])} was witnessed in ${chalk_1.default.green(n)} trace(s) out of ${outcome.samples} explored ${percentage}`);
        });
    }
}
/**
 * Print violated invariants using indices provided by the Rust backend.
 *
 * @param violatedIndices The indices of invariants that were violated.
 * @param invariants The list of invariant names/expressions.
 */
function printViolatedInvariantsByIndex(violatedIndices, invariants) {
    if (violatedIndices.length === 0) {
        return;
    }
    for (const idx of violatedIndices) {
        if (idx < invariants.length) {
            console.log(chalk_1.default.red(`  ❌ ${invariants[idx]}`));
        }
    }
}
/**
 * Print violated invariants in the final state.
 *
 * @param state The final state.
 * @param invariants The list of invariants.
 * @param prev The previous stage context.
 */
function printViolatedInvariants(state, invariants, prev) {
    if (invariants.length <= 1 && prev.args.inductiveInvariant === undefined) {
        return;
    }
    const evaluator = new evaluator_1.Evaluator(prev.resolver.table, (0, trace_1.newTraceRecorder)(0, (0, rng_1.newRng)()), (0, rng_1.newRng)(), false);
    for (const inv of invariants) {
        const invExpr = (0, cliHelpers_1.toExpr)(prev, inv).unwrap();
        evaluator.evaluate(invExpr);
        evaluator.updateState(state);
        const evalResult = evaluator.evaluate(invExpr);
        if (evalResult.isRight() && evalResult.value.kind === 'bool' && !evalResult.value.value) {
            console.log(chalk_1.default.red(`  ❌ ${inv}`));
        }
    }
}
/**
 * Process verification result from TLC.
 */
function processTlcResult(res, startMs, verbosityLevel, stage) {
    const elapsedMs = Date.now() - startMs;
    return res
        .map(() => {
        if (verbosity_1.verbosity.hasResults(verbosityLevel)) {
            console.log('\n' + chalk_1.default.green('[ok]') + ' No violation found ' + chalk_1.default.gray(`(${elapsedMs}ms).`));
        }
        return { ...stage, status: 'ok', errors: [] };
    })
        .mapLeft(err => {
        const status = err.isViolation ? 'violation' : 'failure';
        const summary = err.isViolation ? 'Found an issue' : 'TLC encountered an error';
        if (verbosity_1.verbosity.hasResults(verbosityLevel)) {
            console.log('\n' + chalk_1.default.red(`[${status}]`) + ' ' + summary + ' ' + chalk_1.default.gray(`(${elapsedMs}ms).`));
        }
        return {
            msg: err.explanation,
            stage: { ...stage, status, errors: err.errors },
        };
    });
}
/**
 * Process the result of a verification call.
 *
 * @param res The result of the verification.
 * @param startMs The start time in milliseconds.
 * @param verbosityLevel The verbosity level.
 * @param stage The current tracing stage.
 * @param invariantsList The list of invariants.
 * @param invariantExprs Optional parsed invariant expressions for Rust-based evaluation.
 * @param table Optional lookup table for Rust-based evaluation.
 * @returns The processed result.
 */
async function processApalacheResult(res, startMs, verbosityLevel, stage, invariantsList, invariantExprs, table) {
    const elapsedMs = Date.now() - startMs;
    if (res.isRight()) {
        if (verbosity_1.verbosity.hasResults(verbosityLevel)) {
            console.log(chalk_1.default.green('[ok]') + ' No violation found ' + chalk_1.default.gray(`(${elapsedMs}ms).`));
            if (verbosity_1.verbosity.hasHints(verbosityLevel)) {
                console.log(chalk_1.default.gray('You may increase --max-steps.'));
                console.log(chalk_1.default.gray('Use --verbosity to produce more (or less) output.'));
            }
        }
        return (0, either_1.right)({ ...stage, status: 'ok', errors: [] });
    }
    const err = res.value;
    const trace = err.traces ? (0, itf_1.ofItfNormalized)(err.traces[0]) : undefined;
    const status = trace !== undefined ? 'violation' : 'failure';
    if (trace !== undefined) {
        maybePrintCounterExample(verbosityLevel, trace, [], [], stage.args.hide || []);
        if (verbosity_1.verbosity.hasResults(verbosityLevel)) {
            console.log(chalk_1.default.red(`[${status}]`) + ' Found an issue ' + chalk_1.default.gray(`(${elapsedMs}ms).`));
            const itfStates = err.traces?.[0]?.states;
            const lastItfState = itfStates?.[itfStates.length - 1];
            if (invariantExprs && table && lastItfState) {
                await printViolatedInvariantsWithRust(invariantsList, verbosityLevel, invariantExprs, table, lastItfState);
            }
        }
        if (stage.args.outItf && err.traces) {
            writeToJson(stage.args.outItf, err.traces[0]);
        }
    }
    return (0, either_1.left)({
        msg: err.explanation,
        stage: { ...stage, status, errors: err.errors, trace },
    });
}
/**
 * Print violated invariants using the Rust evaluator.
 */
async function printViolatedInvariantsWithRust(invariantsList, verbosityLevel, invariantExprs, table, itfState) {
    const result = await (0, invariantsReporter_1.findViolatedInvariants)(itfState, table, invariantExprs, verbosityLevel);
    if (result.isRight()) {
        printViolatedInvariantsByIndex(result.value, invariantsList);
    }
    else {
        console.warn(chalk_1.default.yellow(`Warning: could not determine violated invariants: ${result.value.message}`));
    }
}
function outputJson(stage) {
    return jsonStringOfOutputStage(pickOutputStage(stage));
}
function writeOutputToJson(filename, stage) {
    const path = (0, path_1.resolve)((0, process_1.cwd)(), filename);
    (0, fs_1.writeFileSync)(path, outputJson(stage));
}
function jsonStringOfOutputStage(json) {
    return json_bigint_1.default.stringify(json, jsonHelper_1.replacer);
}
/**
 * Write json to a file.
 *
 * @param filename name of the file to write to
 * @param json is an object tree to write
 */
function writeToJson(filename, json) {
    const path = (0, path_1.resolve)((0, process_1.cwd)(), filename);
    (0, fs_1.writeFileSync)(path, jsonStringOfOutputStage(json));
}
// Extract just the parts of a ProcedureStage that we use for the output
// See https://stackoverflow.com/a/39333479/1187277
const pickOutputStage = ({ stage, warnings, modules, table, types, effects, errors, documentation, passed, failed, ignored, status, trace, seed, main, }) => {
    return {
        stage,
        warnings,
        modules,
        table,
        types,
        effects,
        errors,
        documentation,
        passed,
        failed,
        ignored,
        status,
        trace,
        seed,
        main,
    };
};
function cliErr(msg, stage) {
    return (0, either_1.left)({ msg, stage });
}
/**
 * Find the main module by name.
 */
function findMainModule(prev, mainName) {
    return prev.modules.find(m => m.name === mainName);
}
/**
 * Handle errors when the main module is not found.
 */
function handleMainModuleError(prev, mainName) {
    const error = { code: 'QNT405', message: `Main module ${mainName} not found` };
    return cliErr('Argument error', { ...prev, errors: [(0, cliHelpers_1.mkErrorMessage)(prev.sourceMap)(error)] });
}
function prepareOnTrace(source, outputTemplate, nTraces, metadata) {
    return (index, status, vars, states, name) => {
        if (outputTemplate) {
            const filename = name
                ? (0, cliHelpers_1.expandNamedOutputTemplate)(outputTemplate, name, index, { autoAppend: nTraces > 1 })
                : (0, cliHelpers_1.expandOutputTemplate)(outputTemplate, index, { autoAppend: nTraces > 1 });
            const trace = (0, itf_1.toItf)(vars, states, metadata);
            if (trace.isRight()) {
                const jsonObj = (0, cliHelpers_1.addItfHeader)(source, status, trace.value);
                writeToJson(filename, jsonObj);
            }
            else {
                console.error(`ITF conversion failed on ${index}: ${trace.value}`);
            }
        }
    };
}
/**
 * Output test results.
 */
function outputTestResults(results, verbosityLevel, elapsedMs) {
    const out = console.log;
    let nFailures = 1;
    if (verbosity_1.verbosity.hasResults(verbosityLevel)) {
        results.forEach(res => {
            if (res.status === 'passed') {
                out(`    ${chalk_1.default.green('ok')} ${res.name} passed ${res.nsamples} test(s)`);
            }
            else if (res.status === 'failed') {
                const errNo = chalk_1.default.red(nFailures);
                out(`    ${errNo}) ${res.name} failed after ${res.nsamples} test(s)`);
                nFailures++;
            }
            if (res.status !== 'ignored') {
                for (const msgs of res.traces?.at(0)?.diagnostics || []) {
                    for (const msg of msgs) {
                        const doc = (0, prettierimp_1.nest)('       ', [
                            (0, prettierimp_1.text)('       '),
                            (0, prettierimp_1.brackets)((0, prettierimp_1.text)('DEBUG')),
                            prettierimp_1.space,
                            (0, prettierimp_1.text)(msg.label),
                            (0, prettierimp_1.line)(),
                            (0, graphics_1.prettyQuintEx)(msg.value),
                        ]);
                        out((0, prettierimp_1.format)((0, graphics_1.terminalWidth)(), 5, doc));
                    }
                }
            }
        });
        const passed = results.filter(r => r.status === 'passed');
        const failed = results.filter(r => r.status === 'failed');
        const ignored = results.filter(r => r.status === 'ignored');
        out('');
        if (passed.length > 0) {
            out(chalk_1.default.green(`  ${passed.length} passing`) + chalk_1.default.gray(` (${elapsedMs}ms)`));
        }
        if (failed.length > 0) {
            out(chalk_1.default.red(`  ${failed.length} failed`));
        }
        if (ignored.length > 0) {
            out(chalk_1.default.gray(`  ${ignored.length} ignored`));
        }
    }
}
function outputTestErrors(prev, verbosityLevel, failed) {
    const namedErrors = failed.reduce((acc, failure) => acc.concat(failure.errors.map(e => [failure, (0, cliHelpers_1.mkErrorMessage)(prev.sourceMap)(e)])), []);
    const out = console.log;
    // We know that there are errors, so report as required by the verbosity configuration
    if (verbosity_1.verbosity.hasTestDetails(verbosityLevel)) {
        const code = prev.sourceCode;
        const finders = (0, errorReporter_1.createFinders)(code);
        const columns = !prev.args.out ? (0, graphics_1.terminalWidth)() : 80;
        out('');
        namedErrors.forEach(([testResult, err], index) => {
            const details = (0, errorReporter_1.formatError)(code, finders, err);
            // output the header
            out(`  ${index + 1}) ${testResult.name}:`);
            const lines = details.split('\n');
            // output the error lines in red
            lines.filter(l => l.trim().length > 0).forEach(l => out(chalk_1.default.red('      ' + l)));
            if (verbosity_1.verbosity.hasActionTracking(verbosityLevel)) {
                out('');
                // Skip frame display for Rust backend
                if (!testResult.traces) {
                    testResult.frames?.forEach((f, index) => {
                        out(`[${chalk_1.default.bold('Frame ' + index)}]`);
                        const console = {
                            width: columns,
                            out: (s) => process.stdout.write(s),
                        };
                        (0, graphics_1.printExecutionFrameRec)(console, f, []);
                        out('');
                    });
                    if (testResult.frames?.length == 0) {
                        out('    [No execution]');
                    }
                }
            }
            // output the seed
            out(chalk_1.default.gray(`    Use --seed=0x${testResult.seed.toString(16)} --match=${testResult.name} to repeat.`));
        });
        out('');
    }
    if (verbosity_1.verbosity.hasHints(verbosityLevel) && !verbosity_1.verbosity.hasActionTracking(verbosityLevel)) {
        out(chalk_1.default.gray(`\n  Use --verbosity=3 to show executions.`));
        out(chalk_1.default.gray(`  Further debug with: quint test --verbosity=3 ${prev.args.input}`));
    }
}
function printInductiveInvariantProgress(verbosityLevel, args, phase, nPhases, invariantsString = '') {
    if (verbosity_1.verbosity.hasProgress(verbosityLevel)) {
        switch (phase) {
            case 1:
                console.log(chalk_1.default.gray(`> [1/${nPhases}] Checking whether the inductive invariant '${args.inductiveInvariant}' holds in the initial state(s) defined by '${args.init}'...`));
                break;
            case 2:
                console.log(chalk_1.default.gray(`> [2/${nPhases}] Checking whether '${args.step}' preserves the inductive invariant '${args.inductiveInvariant}'...`));
                break;
            case 3:
                console.log(chalk_1.default.gray(`> [3/3] Checking whether the inductive invariant '${args.inductiveInvariant}' implies '${invariantsString}'...`));
                break;
        }
    }
}
//# sourceMappingURL=cliReporting.js.map