--  we may need to verify that in a list at most n elements are in
--  a given state

with Common; use Common; use Common.DLL;

package Test_Astrium_3 is

   procedure Activate_First_Non_Active (L : in out List)
   with Post => Num_Of_Active (L'Old) <= Num_Of_Active(L);

end Test_Astrium_3;
