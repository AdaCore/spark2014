-- Generic_Matrix_Thing
-- Example generic package that uses Ada's generic array package.
pragma SPARK_Mode;

with Ada.Numerics.Generic_Real_Arrays;

generic
    type Real is digits <>;
    SizeA, SizeB: Positive;

package Generic_Matrix_Thing is
    pragma Pure(Generic_Matrix_Thing);

    -- Types -----------------------------------------------------------
    package This_Matrix is new
      Ada.Numerics.Generic_Real_Arrays(Real'Base);

    subtype AxA_Matrix is This_Matrix.Real_Matrix(1..SizeA, 1..SizeA);
    subtype AxB_Matrix is This_Matrix.Real_Matrix(1..SizeA, 1..SizeB);
    subtype BxA_Matrix is This_Matrix.Real_Matrix(1..SizeB, 1..SizeA);
    subtype BxB_Matrix is This_Matrix.Real_Matrix(1..SizeB, 1..SizeB);

    -- Public Methods
    --------------------------------------------------------------------
    -- Manipulate
    -- Perform an example manipulation using array operations.
    function Manipulate( Original: in AxA_Matrix; Map: in AxB_Matrix )
                        return BxB_Matrix with Inline;

end Generic_Matrix_Thing;
