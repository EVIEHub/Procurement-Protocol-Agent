"use strict";
/* ----------------------------------------------------------------------------------
 * Copyright 2021-2022 Informal Systems
 * Licensed under the Apache License, Version 2.0.
 * See LICENSE in the project root for license information.
 * --------------------------------------------------------------------------------- */
Object.defineProperty(exports, "__esModule", { value: true });
exports.unitType = unitType;
exports.isUnitType = isUnitType;
exports.sumType = sumType;
exports.rowFieldNames = rowFieldNames;
exports.typeNames = typeNames;
exports.rowNames = rowNames;
const IRVisitor_1 = require("./IRVisitor");
// A value of the unit type, i.e. an empty record
function unitType(id) {
    return {
        id,
        kind: 'tup',
        fields: { kind: 'row', fields: [], other: { kind: 'empty' } },
    };
}
function isUnitType(r) {
    return r.kind === 'tup' && r.fields.kind === 'row' && r.fields.fields.length === 0 && r.fields.other.kind === 'empty';
}
function sumType(labelTypePairs, rowVar, id) {
    const fields = labelTypePairs.map(([fieldName, fieldType]) => ({ fieldName, fieldType }));
    const other = rowVar ? { kind: 'var', name: rowVar } : { kind: 'empty' };
    return { kind: 'sum', fields: { kind: 'row', fields, other }, id };
}
/*
 * Gives all of a row's field names
 */
function rowFieldNames(r) {
    switch (r.kind) {
        case 'row':
            return r.fields.map(f => f.fieldName).concat(rowFieldNames(r.other));
        case 'var':
        case 'empty':
            return [];
    }
}
/*
 * Collects all type and row variable names from a given type
 *
 * @param t the type to have its names collected
 *
 * @returns the set of type variables and the set of row variables
 */
function typeNames(t) {
    const collector = new TypeNamesCollector();
    (0, IRVisitor_1.walkType)(collector, t);
    return { typeVariables: collector.typeNames, rowVariables: collector.rowNames };
}
/*
 * Collects all row variable names from a given type
 *
 * @param r the row to have its names collected
 *
 * @returns a set with collected names
 */
function rowNames(r) {
    switch (r.kind) {
        case 'row':
            return rowNames(r.other);
        case 'var':
            return new Set([r.name]);
        case 'empty':
            return new Set([]);
    }
}
class TypeNamesCollector {
    constructor() {
        this.typeNames = new Set();
        this.rowNames = new Set();
    }
    exitVarType(t) {
        this.typeNames.add(t.name);
    }
    exitVarRow(t) {
        this.rowNames.add(t.name);
    }
}
//# sourceMappingURL=quintTypes.js.map