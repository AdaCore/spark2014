pragma SPARK_Mode;
pragma Profile( Jorvik );
pragma Partition_Elaboration_Policy( Sequential );

--pragma Restrictions(Simple_Barriers);
--  with Jorvik already enabled
--  the above pragma should not be needed

package P is

    protected type PT is end;

end P;
