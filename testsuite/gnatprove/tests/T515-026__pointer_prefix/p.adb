package body P is
    type Int_Ptr is access Integer;

    type Rec is record
       C : Int_Ptr;
    end record;

    function Create return Int_Ptr with Volatile_Function,
      Post => Create'Result /= null and Create'Result.all <= 1000
    is
    begin
       return new Integer'(3);
    end Create;

    procedure OK3 with Pre => True is
       X : Integer := 1;
       Y : Int_Ptr := new Integer'(3);
       Z : Int_Ptr := new Integer'(3);
    begin
       X := Create.all;
       X := Rec'(if X = 1 then (C => Y) else Rec'(C => Z)).C.all;
    end OK3;
end P;
