package Test is

   protected Single_Protected_Type is
      procedure Dummy_Depends
      with
        Depends => (Single_Protected_Type => Single_Protected_Type);
   end;

end Test;
