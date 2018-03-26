package P with SPARK_Mode is
   package Bad with SPARK_Mode => Off is
      type T is record
         C : Integer;
      end record;
      X : constant T := (C => 0);
   end;
   procedure Dummy;
end;
