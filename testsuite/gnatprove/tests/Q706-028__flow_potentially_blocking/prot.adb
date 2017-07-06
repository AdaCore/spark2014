with Ext;

package body Prot with SPARK_Mode is

   protected body P is
      procedure Read is
      begin
         Count := Count + 1;
         Ext.Proc;
      end Read;
   end P;

end Prot;
