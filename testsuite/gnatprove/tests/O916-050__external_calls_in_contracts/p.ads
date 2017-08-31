package P is

   protected type PT is

      function Internal return Boolean;

      procedure Proc1 with Pre => Internal;
      procedure Proc2 with Contract_Cases => (Internal => Internal);

   end;

end;
