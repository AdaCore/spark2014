package C with SPARK_Mode is

   package Inner with SPARK_Mode => Off is
      X : aliased Integer := 0;
      X_Ptr : access Integer := X'Access;
   end;

   task type TT is
      pragma Priority (Inner.X_Ptr.all); -- not in SPARK
   end;

end;
