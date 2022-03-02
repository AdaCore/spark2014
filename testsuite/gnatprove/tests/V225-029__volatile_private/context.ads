package Context is

   type Raw_Context_Type is limited record
      null;
   end record
   with
      Async_Readers,
      Volatile;

end Context;
