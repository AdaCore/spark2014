-- Debug the reason for "no contextual analysis" messages
--   when nesting generic packages.
pragma SPARK_Mode;

with Generic_Matrix_Thing;
with Specific_Matrix_Other;

procedure Main_Test is
    -- version with nested generics ------------------------------------
    package Specific_Matrix_Thing is new
      Generic_Matrix_Thing( Float, 3, 2 );

    Mat_In : Specific_Matrix_Thing.AxA_Matrix := ((1.0, 0.0, 0.0),
                                                  (0.0, 1.0, 0.0),
                                                  (0.0, 0.0, 1.0));
    Mat_Map: Specific_Matrix_Thing.AxB_Matrix := ((2.0, 0.0),
                                                  (0.0, 0.0),
                                                  (0.0, 3.0));
    Mat_Out: Specific_Matrix_Thing.BxB_Matrix :=
               (others => (others => 0.0));

    use type Specific_Matrix_Thing.BxB_Matrix; -- for assertion

    -- version without nested generics ---------------------------------
    Mat_In2 : Specific_Matrix_Other.AxA_Matrix := ((1.0, 0.0, 0.0),
                                                   (0.0, 1.0, 0.0),
                                                   (0.0, 0.0, 1.0));
    Mat_Map2: Specific_Matrix_Other.AxB_Matrix := ((2.0, 0.0),
                                                   (0.0, 0.0),
                                                   (0.0, 3.0));
    Mat_Out2: Specific_Matrix_Other.BxB_Matrix :=
                (others => (others => 0.0));

    use type Specific_Matrix_Other.BxB_Matrix; -- for assertion

begin
    Mat_Out := Specific_Matrix_Thing.Manipulate( Original => Mat_In,
                                                 Map      => Mat_Map );
    pragma Assert( Mat_Out = ((4.0, 0.0), (0.0, 9.0)) );

    Mat_Out2 := Specific_Matrix_Other.Manipulate( Original => Mat_In2,
                                                  Map      => Mat_Map2);
    pragma Assert( Mat_Out2 = ((4.0, 0.0), (0.0, 9.0)) );
end Main_Test;
