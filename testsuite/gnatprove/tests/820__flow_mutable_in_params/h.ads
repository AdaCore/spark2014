package H with SPARK_Mode is
   type T is private with
     Default_Initial_Condition => False;

   function "=" (X, Y : T) return Boolean;

   procedure P (X : T) with
     Post => X /= Copy (X)'Old;
   pragma Annotate (GNATprove, Mutable_In_Parameters, T);

   procedure P2 (X, Y : T) with
     Post => X /= Copy (X)'Old and Y = Copy (Y)'Old;
   pragma Annotate (GNATprove, Mutable_In_Parameters, T);

   function Copy (X : T) return T with
     Post => X = Copy'Result;

   function New_T return T;

private
   type T is not null access Integer;
end H;
