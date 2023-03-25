use std::collections::HashMap;

use good_lp::{
    self, default_solver, variable, Expression, ProblemVariables, ResolutionError, Solution,
    SolverModel, Variable,
};

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

pub fn solve(sudoku: &[u8; 81]) -> Result<[u8; 81], ResolutionError> {
    let mut problem = ProblemVariables::new();
    let entries = parse_sudoku_to_variables(&sudoku);

    let mut variables_map: HashMap<(u8, u8), Variable> = HashMap::new();
    let mut const_map: HashMap<(u8, u8), u8> = HashMap::new();

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

    for i in 0..81 {
        let expression = (1..=9).fold(Expression::from(0), |acc, v| {
            if let Some(x) = variables_map.get(&(v, i as u8)) {
                acc + x
            } else {
                acc + Expression::from(
                    *const_map
                        .get(&(v, i as u8))
                        .expect("Should be inside const_map if not in variables_map.")
                        as i32,
                )
            }
        });

        constraints.push(expression.eq(1));
    }

    for v in 1..=9 {
        for line in get_lines_indices() {
            let expression = line.iter().fold(Expression::from(0), |acc, i| {
                if let Some(x) = variables_map.get(&(v, *i as u8)) {
                    acc + x
                } else {
                    acc + Expression::from(
                        *const_map
                            .get(&(v, *i as u8))
                            .expect("Should be inside const_map if not in variables_map.")
                            as i32,
                    )
                }
            });
            constraints.push(expression.eq(1));
        }

        for column in get_column_indices() {
            let expression = column.iter().fold(Expression::from(0), |acc, i| {
                if let Some(x) = variables_map.get(&(v, *i as u8)) {
                    acc + x
                } else {
                    acc + Expression::from(
                        *const_map
                            .get(&(v, *i as u8))
                            .expect("Should be inside const_map if not in variables_map.")
                            as i32,
                    )
                }
            });
            constraints.push(expression.eq(1));
        }

        for block in get_blocks() {
            let expression = block.iter().fold(Expression::from(0), |acc, i| {
                if let Some(x) = variables_map.get(&(v, *i as u8)) {
                    acc + x
                } else {
                    acc + Expression::from(
                        *const_map
                            .get(&(v, *i as u8))
                            .expect("Should be inside const_map if not in variables_map.")
                            as i32,
                    )
                }
            });
            constraints.push(expression.eq(1));
        }
    }

    let mut base_problem = problem.maximise(Expression::from(0)).using(default_solver);

    for constraint in constraints {
        base_problem = base_problem.with(constraint);
    }

    let solution = base_problem.solve()?;

    let mut result = [255; 81];

    for i in 0..81 {
        for v in 1..=9 {
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

pub fn parse_sudoku_to_variables(arr: &[u8; 81]) -> HashMap<(u8, u8), SudokuBinary> {
    let mut variables = HashMap::new();
    for possible_value in 1..=9 {
        for k in 0..81 {
            let value_at_k = arr[k];
            if value_at_k == 0 {
                variables.insert(
                    (possible_value as u8, k as u8),
                    SudokuBinary::Variable(variable().binary()),
                );
            } else if value_at_k == possible_value as u8 {
                variables.insert((possible_value as u8, k as u8), SudokuBinary::Constant(1));
            } else if value_at_k < 10 {
                variables.insert((possible_value as u8, k as u8), SudokuBinary::Constant(0));
            } else {
                panic!();
            }
        }
    }

    variables
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

pub fn print_as_sudoku(sudoku: &[u8; 81]) {
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
