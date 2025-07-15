package P is
   protected Obj
     with Priority => 3
   is
      procedure PP1
      with Global => null, Always_Terminates;
   end;
end P;
