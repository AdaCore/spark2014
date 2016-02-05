package C with SPARK_Mode is

   package Inner with SPARK_Mode => Off is
      X : aliased Integer := 0;
      X_Ptr : access Integer := X'Access;
   end;

   task type TT is
      pragma Assert (Inner.X_Ptr = Inner.X_Ptr); -- not in SPARK
   end;

end;
