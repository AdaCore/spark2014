with Remote;

package Q is

   type T is record
     C1 : Integer := Remote.Read_Hidden_Global;  --  NOK
     C2 : Integer := Remote.Read_Hidden_Const;   --  NOK
   end record;

end;
