package No_Primitive_Call with SPARK_Mode is
    type Root is private;
    procedure Init (I : in out Root; C : Natural)
    with Pre => C > 0;
private
    type Root is tagged record
       F : Integer;
    end record;
   procedure Internal (X : in out Root'Class);
end No_Primitive_Call;
