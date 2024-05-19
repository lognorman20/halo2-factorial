use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt, circuit::*, dev::MockProver, halo2curves::pasta::Fp, plonk::*, poly::Rotation
};

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
                let _ = self.config.selector.enable(&mut region, 0);
                let _ = self.config.selector.enable(&mut region, 1);

                let mut a_cell = region.assign_advice_from_instance(
                    || "a",
                    self.config.instance,
                    0,
                    self.config.advice[0],
                    0,
                )?;

                let mut b_cell = region.assign_advice(
                    || "b",
                    self.config.advice[1],
                    0,
                    || a_cell.value().map(|a| *a + F::one()),
                )?;

                for row in 2..nrows {
                    let c_cell = region.assign_advice(
                        || "c",
                        self.config.advice[0],
                        row,
                        || a_cell.value().and_then(|a| b_cell.value().map(|b| *a * *b)),
                    )?;

                    let d_cell = region.assign_advice(
                        || "d",
                        self.config.advice[1],
                        row,
                        || b_cell.value().map(|b| *b - F::one()),
                    )?;

                    a_cell = c_cell;
                    b_cell = d_cell;
                }

                Ok(a_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default, Debug)]
struct FactorialCircuit<F> {
    n: usize,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for FactorialCircuit<F> {
    type Config = FactorialConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FactorialChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = FactorialChip::construct(config);
        let output = chip.calculate(layouter.namespace(|| "chunk"), self.n)?;

        let _ = chip.expose_public(layouter.namespace(|| "expose output"), output, 1);
        Ok(())
    }
}

fn main() {
    let arg = 5;
    let circuit: FactorialCircuit<Fp> = FactorialCircuit {
        n: arg,
        _marker: PhantomData,
    };

    let public_inputs = vec![Fp::from(arg as u64)];
    let k = 4;

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
}
