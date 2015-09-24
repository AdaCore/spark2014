package No_Primitive with SPARK_Mode is
    type Root is private;
    procedure Init (I : in out Root; C : Natural)
    with Pre => C > 0;
private
    pragma SPARK_Mode (Off);
    type Pos_Access is access all Positive;
    type Root is tagged record
       F : Pos_Access;
    end record;
end No_Primitive;
