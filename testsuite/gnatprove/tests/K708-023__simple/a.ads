package A is
   type T is
      record
         A : Integer;
         B : Integer;
      end record;

   type D is new T;
   subtype S is T;

   type P is private;

   subtype SP is P;

   procedure K;

private
   type P is record
      PA : Integer;
      PB : Integer;
   end record;
end A;
