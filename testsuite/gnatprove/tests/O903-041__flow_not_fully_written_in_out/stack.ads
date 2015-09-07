package Stack with
   SPARK_Mode,
   Abstract_State => The_Stack
is
    subtype Element is Positive;

    procedure Pop  (E : out Element) with
      Global  => (In_Out => The_Stack);

    procedure Push (E : in  Element) with
      Global  => (In_Out => The_Stack);
end Stack;
