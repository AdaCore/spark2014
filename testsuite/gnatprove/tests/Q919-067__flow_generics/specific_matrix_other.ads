-- Specific_Matrix_Other
-- Example generic package that uses Ada's generic array package.
pragma SPARK_Mode;

with Ada.Numerics.Generic_Real_Arrays;

package Specific_Matrix_Other is
    pragma Pure(Specific_Matrix_Other);

    -- Types -----------------------------------------------------------
    package This_Matrix is new
      Ada.Numerics.Generic_Real_Arrays(Float);

    subtype AxA_Matrix is This_Matrix.Real_Matrix(1..3, 1..3);
    subtype AxB_Matrix is This_Matrix.Real_Matrix(1..3, 1..2);
    subtype BxA_Matrix is This_Matrix.Real_Matrix(1..2, 1..3);
    subtype BxB_Matrix is This_Matrix.Real_Matrix(1..2, 1..2);

    -- Public Methods
    --------------------------------------------------------------------
    -- Manipulate
    -- Perform an example manipulation using array operations.
    function Manipulate( Original: in AxA_Matrix; Map: in AxB_Matrix )
                        return BxB_Matrix with Inline;

end Specific_Matrix_Other;
