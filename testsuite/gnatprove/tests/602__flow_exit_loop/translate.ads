with SPARK.Containers.Formal.Unbounded_Vectors;

package Translate with
   SPARK_Mode => On
is

    type Input_T is record
        A : Natural;
        B : Natural;
    end record;

    package Input_Vector_Package is new SPARK.Containers.Formal
       .Unbounded_Vectors
       (Index_Type => Natural, Element_Type => Input_T);

    type Output_T is record
        X : Integer;
        Y : Integer;
    end record;

    package Output_Vector_Package is new SPARK.Containers.Formal
       .Unbounded_Vectors
       (Index_Type => Natural, Element_Type => Output_T);

    procedure Translate
       (Input : Input_T; Output : out Output_T; Success : out Boolean);

    procedure Translate
       (Input_Vector  :     Input_Vector_Package.Vector;
        Output_Vector : out Output_Vector_Package.Vector;
        Success       : out Boolean);

end Translate;
