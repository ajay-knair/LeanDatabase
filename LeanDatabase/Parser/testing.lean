import LeanDatabase.Parser.Query
import LeanDatabase.SQLEquiv

open Lean Meta Elab Term LeanDatabase Parser
open LeanDatabase.SQLEquiv

def exSqlQuery := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT Department, AVG(SalesAmount) AS AverageSales FROM CompanySales WHERE Department = \"Hardware\" GROUP BY Department"


elab "exSqlQuery" : term => do
  let (e, _) ← exSqlQuery
  return e

#check exSqlQuery


def exSqlQuery' := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT
    Department,
    AVG(SalesAmount) AS AverageSales FROM CompanySales
GROUP BY Department
HAVING Department = \"Hardware\""


elab "exSqlQuery'" : term => do
  let (e, _) ← exSqlQuery'
  return e

#check exSqlQuery'

-- AND is commutative in a `WHERE` clause.
def exSqlQuery2 := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT * FROM CompanySales WHERE Department = \"Hardware\" AND SalesAmount > 500"

elab "exSqlQuery2" : term => do
  let (e, _) ← exSqlQuery2
  return e

#check exSqlQuery2

def exSqlQuery2' := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT * FROM CompanySales WHERE SalesAmount > 500 AND Department = \"Hardware\""

elab "exSqlQuery2'" : term => do
  let (e, _) ← exSqlQuery2'
  return e

#check exSqlQuery2'

-- Double negation.
def exSqlQuery3 := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT * FROM CompanySales WHERE NOT (NOT (Year = 2023))"

elab "exSqlQuery3" : term => do
  let (e, _) ← exSqlQuery3
  return e

#check exSqlQuery3

def exSqlQuery3' := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT * FROM CompanySales WHERE Year = 2023"

elab "exSqlQuery3'" : term => do
  let (e, _) ← exSqlQuery3'
  return e

#check exSqlQuery3'

-- AND is idempotent.
def exSqlQuery4 := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT * FROM CompanySales WHERE Department = \"Hardware\" AND Department = \"Hardware\""

elab "exSqlQuery4" : term => do
  let (e, _) ← exSqlQuery4
  return e

#check exSqlQuery4

def exSqlQuery4' := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT * FROM CompanySales WHERE Department = \"Hardware\""

elab "exSqlQuery4'" : term => do
  let (e, _) ← exSqlQuery4'
  return e

#check exSqlQuery4'

-- OR is commutative in a `WHERE` clause.
def exSqlQuery5 := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT * FROM CompanySales WHERE Department = \"Hardware\" OR Year = 2023"

elab "exSqlQuery5" : term => do
  let (e, _) ← exSqlQuery5
  return e

#check exSqlQuery5

def exSqlQuery5' := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT * FROM CompanySales WHERE Year = 2023 OR Department = \"Hardware\""

elab "exSqlQuery5'" : term => do
  let (e, _) ← exSqlQuery5'
  return e

#check exSqlQuery5'

-- De Morgan's law.
def exSqlQuery6 := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT * FROM CompanySales WHERE NOT (Department = \"Hardware\" OR Year = 2023)"

elab "exSqlQuery6" : term => do
  let (e, _) ← exSqlQuery6
  return e

#check exSqlQuery6

def exSqlQuery6' := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT * FROM CompanySales WHERE NOT (Department = \"Hardware\") AND NOT (Year = 2023)"

elab "exSqlQuery6'" : term => do
  let (e, _) ← exSqlQuery6'
  return e

#check exSqlQuery6'

-- `WHERE` before `GROUP BY` vs. an equivalent `HAVING` on the grouping key, with `SUM` instead of `AVG`.
def exSqlQuery7 := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT Year, SUM(SalesAmount) AS TotalSales FROM CompanySales WHERE Year = 2023 GROUP BY Year"

elab "exSqlQuery7" : term => do
  let (e, _) ← exSqlQuery7
  return e

#check exSqlQuery7

def exSqlQuery7' := parseSqlQuery [(`CompanySales, [(`SaleID, .int), (`Department, .string), (`Year, .int),(`SalesAmount, .int)])] "SELECT
    Year,
    SUM(SalesAmount) AS TotalSales FROM CompanySales
GROUP BY Year
HAVING Year = 2023"

elab "exSqlQuery7'" : term => do
  let (e, _) ← exSqlQuery7'
  return e

#check exSqlQuery7'

example: exSqlQuery7 = exSqlQuery7' := by
  sql_equiv
