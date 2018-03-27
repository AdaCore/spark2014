package Q with SPARK_Mode is
   package Bad with SPARK_Mode => Off, Initializes => X is
      type T is record
         C : Integer;
      end record;
      X : constant T := (C => 0);
      procedure Dummy;
   end;
   procedure Dummy;
end;
