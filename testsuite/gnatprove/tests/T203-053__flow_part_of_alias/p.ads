package P is
   type T is record
      C : Integer;
   end record;

   procedure Swap (A, B : in out T);

   protected PT is
      procedure Proc;
   end;
   Part : T := (C => 0) with Part_Of => PT;
end;
