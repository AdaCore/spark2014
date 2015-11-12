package Pre_Should_Hold is
   protected Prot_Int is
      function Is_Positive return Boolean;

      entry Increase
        with Pre  => Is_Positive,
             Post => Is_Positive;
   private
      Condition : Boolean := True;
      The_Int   : Integer := 1;
   end Prot_Int;
end Pre_Should_Hold;
