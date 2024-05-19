use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt, circuit::*, halo2curves::pasta::Fp, plonk::*, poly::Rotation,
};

#[derive(Clone)]
struct Number<F: FieldExt>(AssignedCell<F, F>);

#[derive(Debug, Clone)]
struct FactorialConfig {
    pub advice: [Column<Advice>; 2],
    pub selector: Selector,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct FactorialChip<F: FieldExt> {
    config: FactorialConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FactorialChip<F> {
    pub fn construct(config: FactorialConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> FactorialConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(instance);

        meta.create_gate("factorial", |meta| {
            //
            // col_a   |   col_b   |   selector
            //   a     |     b     |      s
            //   c     |     d     |      ?
            //
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_a, Rotation::next());
            let d = meta.query_advice(col_b, Rotation::next());

            // constraints:
            // b - (d + 1) == 0
            // c - (a * b) == 0
            vec![s * ((b.clone() - (d + Expression::Constant(F::one()))) + (c - (a * b)))]
        });

        FactorialConfig {
            advice: [col_a, col_b],
            selector,
            instance,
        }
    }

    pub fn calculate(
        &self,
        mut layouter: impl Layouter<F>,
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "factorial table",
            |mut region| {
                self.config.selector.enable(&mut region, 0);
                self.config.selector.enable(&mut region, 1);

                let mut a_cell = region.assign_advice_from_instance(
                    || "a",
                    self.config.instance,
                    0,
                    self.config.advice[0],
                    0,
                ).map(Number)?;

                let mut b_cell = region.assign_advice(
                    || "b",
                    self.config.advice[1],
                    0,
                    || a_cell.0.value().map(|a| *a + F::one())
                ).map(Number)?;

                for row in 2..nrows {
                    let c_cell = region.assign_advice(
                        || "c",
                        self.config.advice[0],
                        row,
                        || a_cell.0.value().and_then(|a| b_cell.0.value().map(|b| *a * *b))
                    ).map(Number)?;

                    let d_cell: AssignedCell<F, F> = region.assign_advice(
                        || "d",
                        self.config.advice[1],
                        row,
                        || b_cell.value().into() - Fp::one(), // problem line prolly
                    )?;

                    a_cell = c_cell;
                    b_cell = d_cell;
                }

                Ok()
            },
        )
    }
}

fn main() {
    println!("SPOTEMGOTEM");
}
