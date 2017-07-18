pragma SPARK_Mode;
pragma Profile( GNAT_Extended_Ravenscar );
pragma Partition_Elaboration_Policy( Sequential );

--pragma Restrictions(Simple_Barriers);
--  with GNAT_Extended_Ravenscar already enabled
--  the above pragma should not be needed

package P is

    protected type PT is end;

end P;
