use std::{collections::HashMap, num::ParseIntError};

use good_lp::{
    self, default_solver, variable, Expression, ProblemVariables, ResolutionError, Solution,
    SolverModel, Variable,
};

const SUM_CONSTRAINT: u8 = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9;

#[derive(Debug)]
pub struct Sudoku {
    entries: [SudokuEntry; 81],
}

impl Default for Sudoku {
    fn default() -> Self {
        Sudoku {
            entries: [
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
                SudokuEntry::Constant(1),
            ],
        }
    }
}

#[derive(Debug)]
enum SudokuEntry {
    Variable(good_lp::VariableDefinition),
    Constant(u8),
}

impl Default for SudokuEntry {
    fn default() -> Self {
        SudokuEntry::Constant(1)
    }
}

pub fn solve(sudoku: Sudoku) -> Result<[u8; 81], ResolutionError> {
    let mut problem = ProblemVariables::new();
    let entries = sudoku.entries;

    let mut variables_map: HashMap<usize, Variable> = HashMap::new();
    let mut const_map: HashMap<usize, u8> = HashMap::new();

    for (i, entry) in entries.into_iter().enumerate() {
        match entry {
            SudokuEntry::Variable(x) => {
                variables_map.insert(i, problem.add(x));
                ()
            }
            SudokuEntry::Constant(x) => {
                const_map.insert(i, x);
                ()
            }
        }
    }

    let mut constraints = Vec::new();

    for line in get_lines_indices() {
        let expression = line.iter().fold(Expression::from(0), |acc, i| {
            if let Some(x) = variables_map.get(i) {
                acc + x
            } else {
                acc + Expression::from(
                    *const_map
                        .get(i)
                        .expect("Should be inside const_map if not in variables_map.")
                        as i32,
                )
            }
        });
        constraints.push(expression.eq(SUM_CONSTRAINT));
    }

    for column in get_column_indices() {
        let expression = column.iter().fold(Expression::from(0), |acc, i| {
            if let Some(x) = variables_map.get(i) {
                acc + x
            } else {
                acc + Expression::from(
                    *const_map
                        .get(i)
                        .expect("Should be inside const_map if not in variables_map.")
                        as i32,
                )
            }
        });
        constraints.push(expression.eq(SUM_CONSTRAINT));
    }

    for block in get_blocks() {
        let expression = block.iter().fold(Expression::from(0), |acc, i| {
            if let Some(x) = variables_map.get(i) {
                acc + x
            } else {
                acc + Expression::from(
                    *const_map
                        .get(i)
                        .expect("Should be inside const_map if not in variables_map.")
                        as i32,
                )
            }
        });
        constraints.push(expression.eq(SUM_CONSTRAINT));
    }

    let mut base_problem = problem.maximise(Expression::from(0)).using(default_solver);

    for constraint in constraints {
        base_problem = base_problem.with(constraint);
    }

    let solution = base_problem.solve()?;

    let mut result = [0; 81];

    for i in 0..81 {
        if let Some(x) = variables_map.get(&(i as usize)) {
            result[i] = solution.value(*x) as u8;
        } else {
            let value = const_map
                .get(&(i as usize))
                .expect("Should be inside const_map if not in variables_map.");
            result[i] = *value;
        }
    }

    Ok(result)
}

pub fn read_sudoku(arr: [&str; 81]) -> Result<Sudoku, ParseIntError> {
    let sudoku_entry = Sudoku::default();
    let mut entries = sudoku_entry.entries;

    for (i, entry) in arr.iter().enumerate() {
        let x = entry.parse::<u8>()?;
        if x == 0 {
            entries[i] = SudokuEntry::Variable(variable().integer().min(1).max(9));
        } else if x < 10 {
            entries[i] = SudokuEntry::Constant(x);
        }
    }

    Ok(Sudoku { entries })
}

fn get_lines_indices() -> Vec<Vec<usize>> {
    let mut result = Vec::new();

    for k in 0..9 {
        result.push((0..9).map(|i| 9 * k + i).collect());
    }

    result
}

fn get_column_indices() -> Vec<Vec<usize>> {
    let mut result = Vec::new();

    for k in 0..9 {
        result.push((0..9).map(|i| k + 9 * i).collect());
    }

    result
}

fn get_blocks() -> Vec<Vec<usize>> {
    let mut result = Vec::new();

    for i in 0..3 {
        for j in 0..3 {
            result.push(
                (0..9)
                    .map(|k| get_index_by_coordinate(3 * i + k % 3, 3 * j + k / 3))
                    .collect(),
            )
        }
    }

    result
}

fn get_index_by_coordinate(x: usize, y: usize) -> usize {
    x + 9 * y
}

fn print_as_sudoku(sudoku: &[u8; 81]) {
    for i in 0..9 {
        println!("{:?}", &sudoku[9 * i..9 * (i + 1)])
    }
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_min() {
        let sudoku = read_sudoku([
            "0", "0", "2", "0", "5", "0", "0", "0", "6", "0", "0", "0", "0", "0", "4", "0", "7",
            "0", "1", "0", "8", "0", "9", "0", "0", "0", "0", "0", "0", "0", "7", "0", "6", "0",
            "8", "0", "7", "0", "6", "0", "0", "0", "2", "0", "4", "0", "8", "0", "5", "0", "2",
            "0", "0", "0", "0", "0", "0", "0", "1", "0", "3", "0", "8", "0", "9", "0", "4", "0",
            "0", "0", "0", "0", "8", "0", "0", "0", "2", "0", "4", "0", "0",
        ])
        .unwrap();

        let result = solve(sudoku).unwrap();
        print_as_sudoku(&result);
    }
}
