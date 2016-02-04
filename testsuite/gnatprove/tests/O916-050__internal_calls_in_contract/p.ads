package P is

   protected type PT is

      function Internal return Boolean;

      procedure Proc1 with Post => Internal;
      procedure Proc2 with Contract_Cases => (True => Internal);

   end;

end;
