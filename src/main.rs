use std::collections::HashMap;

use good_lp::{
    self, default_solver, variable, Constraint, Expression, ProblemVariables, ResolutionError,
    Solution, SolverModel, Variable,
};

const ENTRIES_NUMBER: usize = 81;

// Coincides with line and column number. Should equal sqrt of ENTRIES_NUMBER.
const BLOCK_NUMBER: u8 = 9;

#[derive(Debug)]
pub enum SudokuBinary {
    Variable(good_lp::VariableDefinition),
    Constant(u8),
}

impl Default for SudokuBinary {
    fn default() -> Self {
        SudokuBinary::Constant(1)
    }
}

pub fn solve(sudoku: &[u8; ENTRIES_NUMBER]) -> Result<[u8; ENTRIES_NUMBER], ResolutionError> {
    let mut problem = ProblemVariables::new();
    let entries = parse_sudoku_to_variables(&sudoku);

    let mut variables_map: HashMap<(u8, usize), Variable> = HashMap::new();
    let mut const_map: HashMap<(u8, usize), u8> = HashMap::new();

    for (i, entry) in entries.into_iter() {
        match entry {
            SudokuBinary::Variable(x) => {
                variables_map.insert(i, problem.add(x));
            }
            SudokuBinary::Constant(x) => {
                const_map.insert(i, x);
            }
        }
    }

    let mut constraints = Vec::new();

    for i in 0..ENTRIES_NUMBER {
        let constraint = get_constraint_of_uniqueness_in_square(&variables_map, i, &const_map);

        constraints.push(constraint);
    }

    for v in 1..=BLOCK_NUMBER {
        for line in get_lines_indices() {
            let constraint = get_line_constraint(line, &variables_map, v, &const_map);

            constraints.push(constraint);
        }

        for column in get_column_indices() {
            let constraint = get_column_constraint(column, &variables_map, v, &const_map);

            constraints.push(constraint);
        }

        for block in get_blocks() {
            let constraint = get_block_constraint(block, &variables_map, v, &const_map);

            constraints.push(constraint);
        }
    }

    let mut base_problem = problem.maximise(Expression::from(0)).using(default_solver);

    for constraint in constraints {
        base_problem = base_problem.with(constraint);
    }

    let solution = base_problem.solve()?;

    let mut result = [255; ENTRIES_NUMBER];

    for i in 0..ENTRIES_NUMBER {
        for v in 1..=BLOCK_NUMBER {
            if let Some(x) = variables_map.get(&(v, i)) {
                let binary_value = solution.value(*x);
                if binary_value == 1. {
                    result[i as usize] = v;
                }
            } else {
                let binary_value = const_map
                    .get(&(v, i))
                    .expect("Should be inside const_map if not in variables_map.");
                if *binary_value == 1 {
                    result[i as usize] = v;
                }
            }
        }
    }

    Ok(result)
}

/// Creates constraint that makes the given block have only non-repeated values.
fn get_block_constraint(
    block: Vec<usize>,
    variables_map: &HashMap<(u8, usize), Variable>,
    v: u8,
    const_map: &HashMap<(u8, usize), u8>,
) -> Constraint {
    let expression = block.iter().fold(Expression::from(0), |acc, i| {
        if let Some(x) = variables_map.get(&(v, *i)) {
            acc + x
        } else {
            acc + Expression::from(
                *const_map
                    .get(&(v, *i))
                    .expect("Should be inside const_map if not in variables_map.")
                    as i32,
            )
        }
    });
    expression.eq(1)
}

/// Creates constraint that makes the given column have only non-repeated values.
fn get_column_constraint(
    column: Vec<usize>,
    variables_map: &HashMap<(u8, usize), Variable>,
    v: u8,
    const_map: &HashMap<(u8, usize), u8>,
) -> Constraint {
    let expression = column.iter().fold(Expression::from(0), |acc, i| {
        if let Some(x) = variables_map.get(&(v, *i)) {
            acc + x
        } else {
            acc + Expression::from(
                *const_map
                    .get(&(v, *i))
                    .expect("Should be inside const_map if not in variables_map.")
                    as i32,
            )
        }
    });
    expression.eq(1)
}

/// Creates constraint that makes the given line have only non-repeated values.
fn get_line_constraint(
    line: Vec<usize>,
    variables_map: &HashMap<(u8, usize), Variable>,
    v: u8,
    const_map: &HashMap<(u8, usize), u8>,
) -> Constraint {
    let expression = line.iter().fold(Expression::from(0), |acc, i| {
        if let Some(x) = variables_map.get(&(v, *i)) {
            acc + x
        } else {
            acc + Expression::from(
                *const_map
                    .get(&(v, *i))
                    .expect("Should be inside const_map if not in variables_map.")
                    as i32,
            )
        }
    });
    expression.eq(1)
}

/// Creates constraint that makes a given square have an unique value.
fn get_constraint_of_uniqueness_in_square(
    variables_map: &HashMap<(u8, usize), Variable>,
    i: usize,
    const_map: &HashMap<(u8, usize), u8>,
) -> Constraint {
    let expression = (1..=BLOCK_NUMBER).fold(Expression::from(0), |acc, v| {
        if let Some(x) = variables_map.get(&(v, i)) {
            acc + x
        } else {
            acc + Expression::from(
                *const_map
                    .get(&(v, i))
                    .expect("Should be inside const_map if not in variables_map.")
                    as i32,
            )
        }
    });
    expression.eq(1)
}

pub fn parse_sudoku_to_variables(arr: &[u8; ENTRIES_NUMBER]) -> HashMap<(u8, usize), SudokuBinary> {
    let mut variables = HashMap::new();
    for possible_value in 1..=BLOCK_NUMBER {
        for k in 0..ENTRIES_NUMBER {
            let value_at_k = arr[k];
            if value_at_k == 0 {
                variables.insert(
                    (possible_value as u8, k),
                    SudokuBinary::Variable(variable().binary()),
                );
            } else if value_at_k == possible_value as u8 {
                variables.insert((possible_value as u8, k), SudokuBinary::Constant(1));
            } else if value_at_k < 10 {
                variables.insert((possible_value as u8, k), SudokuBinary::Constant(0));
            } else {
                panic!();
            }
        }
    }

    variables
}

fn get_lines_indices() -> Vec<Vec<usize>> {
    let mut result = Vec::new();

    for k in 0..BLOCK_NUMBER {
        result.push(
            (0..BLOCK_NUMBER)
                .map(|i| (BLOCK_NUMBER * k + i) as usize)
                .collect(),
        );
    }

    result
}

fn get_column_indices() -> Vec<Vec<usize>> {
    let mut result = Vec::new();

    for k in 0..BLOCK_NUMBER {
        result.push(
            (0..BLOCK_NUMBER)
                .map(|i| (k + BLOCK_NUMBER * i) as usize)
                .collect(),
        );
    }

    result
}

fn get_blocks() -> Vec<Vec<usize>> {
    let mut result = Vec::new();

    for i in 0..3 {
        for j in 0..3 {
            result.push(
                (0..BLOCK_NUMBER)
                    .map(|k| {
                        get_index_by_coordinate(
                            3 * i as usize + k as usize % 3,
                            3 * j as usize + k as usize / 3,
                        )
                    })
                    .collect(),
            )
        }
    }

    result
}

fn get_index_by_coordinate(x: usize, y: usize) -> usize {
    x + (BLOCK_NUMBER as usize) * y
}

pub fn print_as_sudoku(sudoku: &[u8; ENTRIES_NUMBER]) {
    for i in 0..BLOCK_NUMBER {
        println!(
            "{:?}",
            &sudoku[BLOCK_NUMBER as usize * i as usize..BLOCK_NUMBER as usize * (i as usize + 1)]
        )
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
        let sudoku = [
            0, 0, 2, 0, 5, 0, 0, 0, 6, 0, 0, 0, 0, 0, 4, 0, 7, 0, 1, 0, 8, 0, 9, 0, 0, 0, 0, 0, 0,
            0, 7, 0, 6, 0, 8, 0, 7, 0, 6, 0, 0, 0, 2, 0, 4, 0, 8, 0, 5, 0, 2, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 3, 0, 8, 0, 9, 0, 4, 0, 0, 0, 0, 0, 8, 0, 0, 0, 2, 0, 4, 0, 0,
        ];

        print_as_sudoku(&sudoku);

        // dbg!(get_lines_indices());
        // dbg!(get_column_indices());
        // dbg!(get_blocks());
        // println!("{:?}", parse_sudoku_to_variables(&sudoku));

        let result = solve(&sudoku).unwrap();
        print_as_sudoku(&result);
    }
}
