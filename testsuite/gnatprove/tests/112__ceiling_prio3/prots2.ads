with prots;

package Prots2 is

   protected PO
     with Priority => 6
   is
      procedure PP1
      with Always_Terminates;
      procedure PP2
      with Always_Terminates;
      procedure PP3
      with Always_Terminates;
   end;

end Prots2;
