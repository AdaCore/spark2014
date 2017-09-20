-- Generic_Matrix_Thing
-- Example generic package that uses Ada's generic array package.
pragma SPARK_Mode;

package body Generic_Matrix_Thing is

    --------------------------------------------------------------------
    -- Manipulate
    -- Perform an example manipulation using array operations.
    use This_Matrix; -- for matrix operators
    function Manipulate( Original: in AxA_Matrix; Map: in AxB_Matrix )
                        return BxB_Matrix
    is ( This_Matrix.Transpose( Map ) * Original * Map );

end Generic_Matrix_Thing;
