#include "runtime.h"

clc_ptr lam_29584(clc_ptr _29583, clc_env env)
{
  
  
  return _29583;
}

clc_ptr lam_29592(clc_ptr _29588, clc_env env)
{
  clc_ptr succ_c5_29591; clc_ptr tmp_29589; clc_ptr tmp_29590;
  instr_call(&tmp_29589, env[3], env[2]);
  instr_call(&tmp_29590, tmp_29589, _29588);
  instr_struct(&succ_c5_29591, 5, 1,
    tmp_29590);
  return succ_c5_29591;
}

clc_ptr addn_29594(clc_ptr _29580, clc_env env)
{
  clc_ptr _29586; clc_ptr case_29581; clc_ptr clo_29585; clc_ptr clo_29593;
  switch(((clc_node)_29580)->tag){
    case 4:
      instr_clo(&clo_29585, &lam_29584, 2, env, 1, _29580);
      instr_mov(&case_29581, clo_29585);
      break;
    case 5:
      instr_mov(&_29586, ((clc_node)_29580)->data[0]);
      instr_clo(&clo_29593, &lam_29592, 2, env, 2, _29580, _29586);
      instr_mov(&case_29581, clo_29593);
      break;}
  return case_29581;
}

clc_ptr lam_29602(clc_ptr _29600, clc_env env)
{
  clc_ptr zero_c4_29601;
  instr_struct(&zero_c4_29601, 4, 0);
  return zero_c4_29601;
}

clc_ptr lam_29612(clc_ptr _29606, clc_env env)
{
  clc_ptr _29609; clc_ptr case_29607; clc_ptr succ_c5_29608;
  clc_ptr tmp_29610; clc_ptr tmp_29611;
  switch(((clc_node)_29606)->tag){
    case 4:
      instr_struct(&succ_c5_29608, 5, 1,
        env[2]);
      instr_mov(&case_29607, succ_c5_29608);
      break;
    case 5:
      instr_mov(&_29609, ((clc_node)_29606)->data[0]);
      instr_call(&tmp_29610, env[3], env[2]);
      instr_call(&tmp_29611, tmp_29610, _29609);
      instr_mov(&case_29607, tmp_29611);
      break;}
  return case_29607;
}

clc_ptr subn_29614(clc_ptr _29597, clc_env env)
{
  clc_ptr _29604; clc_ptr case_29598; clc_ptr clo_29603; clc_ptr clo_29613;
  switch(((clc_node)_29597)->tag){
    case 4:
      instr_clo(&clo_29603, &lam_29602, 3, env, 1, _29597);
      instr_mov(&case_29598, clo_29603);
      break;
    case 5:
      instr_mov(&_29604, ((clc_node)_29597)->data[0]);
      instr_clo(&clo_29613, &lam_29612, 3, env, 2, _29597, _29604);
      instr_mov(&case_29598, clo_29613);
      break;}
  return case_29598;
}

clc_ptr lam_29621(clc_ptr _29620, clc_env env)
{
  
  
  return _29620;
}

clc_ptr lam_29630(clc_ptr _29626, clc_env env)
{
  clc_ptr String_c18_29629; clc_ptr tmp_29627; clc_ptr tmp_29628;
  instr_call(&tmp_29627, env[4], env[3]);
  instr_call(&tmp_29628, tmp_29627, _29626);
  instr_struct(&String_c18_29629, 18, 2,
    env[2], tmp_29628);
  return String_c18_29629;
}

clc_ptr cat_29632(clc_ptr _29617, clc_env env)
{
  clc_ptr _29623; clc_ptr _29624; clc_ptr case_29618; clc_ptr clo_29622;
  clc_ptr clo_29631;
  switch(((clc_node)_29617)->tag){
    case 17:
      instr_clo(&clo_29622, &lam_29621, 4, env, 1, _29617);
      instr_mov(&case_29618, clo_29622);
      break;
    case 18:
      instr_mov(&_29623, ((clc_node)_29617)->data[0]);
      instr_mov(&_29624, ((clc_node)_29617)->data[1]);
      instr_clo(&clo_29631, &lam_29630, 4, env, 3, _29617, _29623, _29624);
      instr_mov(&case_29618, clo_29631);
      break;}
  return case_29618;
}

clc_ptr strlen_29642(clc_ptr _29635, clc_env env)
{
  clc_ptr _29638; clc_ptr _29639; clc_ptr case_29636; clc_ptr succ_c5_29641;
  clc_ptr tmp_29640; clc_ptr zero_c4_29637;
  switch(((clc_node)_29635)->tag){
    case 17:
      instr_struct(&zero_c4_29637, 4, 0);
      instr_mov(&case_29636, zero_c4_29637);
      break;
    case 18:
      instr_mov(&_29638, ((clc_node)_29635)->data[0]);
      instr_mov(&_29639, ((clc_node)_29635)->data[1]);
      instr_call(&tmp_29640, env[0], _29639);
      instr_struct(&succ_c5_29641, 5, 1,
        tmp_29640);
      instr_mov(&case_29636, succ_c5_29641);
      break;}
  return case_29636;
}

clc_ptr lam_29648(clc_ptr _29647, clc_env env)
{
  
  
  return 0;
}

clc_ptr lt_29650(clc_ptr _29645, clc_env env)
{
  clc_ptr clo_29649;
  instr_clo(&clo_29649, &lam_29648, 6, env, 1, _29645);
  return clo_29649;
}

clc_ptr stdin_rec_29655(clc_ptr _29653, clc_env env)
{
  clc_ptr case_29654;
  switch(((clc_node)_29653)->tag){
    case 1: instr_mov(&case_29654, 0);
            break;}
  return case_29654;
}

clc_ptr stdout_rec_29660(clc_ptr _29658, clc_env env)
{
  clc_ptr case_29659;
  switch(((clc_node)_29658)->tag){
    case 1: instr_mov(&case_29659, 0);
            break;}
  return case_29659;
}

clc_ptr stderr_rec_29665(clc_ptr _29663, clc_env env)
{
  clc_ptr case_29664;
  switch(((clc_node)_29663)->tag){
    case 1: instr_mov(&case_29664, 0);
            break;}
  return case_29664;
}

clc_ptr readline_29679(clc_ptr _29674, clc_env env)
{
  clc_ptr recv_struct_29678; clc_ptr send_clo_29675; clc_ptr tmp_29677;
  clc_ptr true_c2_29676;
  instr_send(&send_clo_29675, _29674);
  instr_struct(&true_c2_29676, 2, 0);
  instr_call(&tmp_29677, send_clo_29675, true_c2_29676);
  instr_free_clo(send_clo_29675);
  instr_recv(&recv_struct_29678, tmp_29677, 13);
  return recv_struct_29678;
}

clc_ptr close_in_29687(clc_ptr _29682, clc_env env)
{
  clc_ptr false_c3_29685; clc_ptr send_clo_29684; clc_ptr tmp_29686;
  clc_ptr unit_struct_29683;
  instr_send(&send_clo_29684, _29682);
  instr_struct(&false_c3_29685, 3, 0);
  instr_call(&tmp_29686, send_clo_29684, false_c3_29685);
  instr_free_clo(send_clo_29684);
  instr_struct(&unit_struct_29683, 1, 0);
  return unit_struct_29683;
}

clc_ptr lam_29698(clc_ptr _29692, clc_env env)
{
  clc_ptr send_clo_29693; clc_ptr send_clo_29696; clc_ptr tmp_29695;
  clc_ptr tmp_29697; clc_ptr true_c2_29694;
  instr_send(&send_clo_29693, env[1]);
  instr_struct(&true_c2_29694, 2, 0);
  instr_call(&tmp_29695, send_clo_29693, true_c2_29694);
  instr_free_clo(send_clo_29693);
  instr_send(&send_clo_29696, tmp_29695);
  instr_call(&tmp_29697, send_clo_29696, _29692);
  instr_free_clo(send_clo_29696);
  return tmp_29697;
}

clc_ptr printline_29700(clc_ptr _29690, clc_env env)
{
  clc_ptr clo_29699;
  instr_clo(&clo_29699, &lam_29698, 15, env, 1, _29690);
  return clo_29699;
}

clc_ptr close_out_29708(clc_ptr _29703, clc_env env)
{
  clc_ptr false_c3_29706; clc_ptr send_clo_29705; clc_ptr tmp_29707;
  clc_ptr unit_struct_29704;
  instr_send(&send_clo_29705, _29703);
  instr_struct(&false_c3_29706, 3, 0);
  instr_call(&tmp_29707, send_clo_29705, false_c3_29706);
  instr_free_clo(send_clo_29705);
  instr_struct(&unit_struct_29704, 1, 0);
  return unit_struct_29704;
}

clc_ptr lam_29719(clc_ptr _29713, clc_env env)
{
  clc_ptr send_clo_29714; clc_ptr send_clo_29717; clc_ptr tmp_29716;
  clc_ptr tmp_29718; clc_ptr true_c2_29715;
  instr_send(&send_clo_29714, env[1]);
  instr_struct(&true_c2_29715, 2, 0);
  instr_call(&tmp_29716, send_clo_29714, true_c2_29715);
  instr_free_clo(send_clo_29714);
  instr_send(&send_clo_29717, tmp_29716);
  instr_call(&tmp_29718, send_clo_29717, _29713);
  instr_free_clo(send_clo_29717);
  return tmp_29718;
}

clc_ptr printerr_29721(clc_ptr _29711, clc_env env)
{
  clc_ptr clo_29720;
  instr_clo(&clo_29720, &lam_29719, 17, env, 1, _29711);
  return clo_29720;
}

clc_ptr close_err_29729(clc_ptr _29724, clc_env env)
{
  clc_ptr false_c3_29727; clc_ptr send_clo_29726; clc_ptr tmp_29728;
  clc_ptr unit_struct_29725;
  instr_send(&send_clo_29726, _29724);
  instr_struct(&false_c3_29727, 3, 0);
  instr_call(&tmp_29728, send_clo_29726, false_c3_29727);
  instr_free_clo(send_clo_29726);
  instr_struct(&unit_struct_29725, 1, 0);
  return unit_struct_29725;
}

clc_ptr ref_t_29733(clc_ptr _29732, clc_env env)
{
  
  
  return 0;
}

clc_ptr lam_29760(clc_ptr _29753, clc_env env)
{
  clc_ptr _29756; clc_ptr case_29754; clc_ptr tmp_29757; clc_ptr tmp_29758;
  clc_ptr tmp_29759; clc_ptr x_29755;
  switch(((clc_node)_29753)->tag){
    case 13:
      instr_mov(&x_29755, ((clc_node)_29753)->data[0]);
      instr_mov(&_29756, ((clc_node)_29753)->data[1]);
      instr_free_struct(_29753);
      instr_call(&tmp_29757, env[10], env[9]);
      instr_call(&tmp_29758, tmp_29757, x_29755);
      instr_call(&tmp_29759, tmp_29758, _29756);
      instr_free_clo(tmp_29758);
      instr_mov(&case_29754, tmp_29759);
      break;}
  return case_29754;
}

clc_ptr lam_29765(clc_ptr _29742, clc_env env)
{
  clc_ptr _29745; clc_ptr case_29743; clc_ptr case_29746; clc_ptr clo_29761;
  clc_ptr recv_struct_29762; clc_ptr send_clo_29749; clc_ptr tmp_29747;
  clc_ptr tmp_29748; clc_ptr tmp_29750; clc_ptr tmp_29751; clc_ptr tmp_29763;
  clc_ptr unit_struct_29764; clc_ptr x_29744;
  switch(((clc_node)_29742)->tag){
    case 13:
      instr_mov(&x_29744, ((clc_node)_29742)->data[0]);
      instr_mov(&_29745, ((clc_node)_29742)->data[1]);
      instr_free_struct(_29742);
      switch(((clc_node)x_29744)->tag){
        case 22:
          instr_call(&tmp_29747, env[6], env[5]);
          instr_call(&tmp_29748, tmp_29747, env[3]);
          instr_send(&send_clo_29749, _29745);
          instr_call(&tmp_29750, send_clo_29749, env[3]);
          instr_free_clo(send_clo_29749);
          instr_call(&tmp_29751, tmp_29748, tmp_29750);
          instr_free_clo(tmp_29748);
          instr_mov(&case_29746, tmp_29751);
          break;
        case 23:
          instr_clo(&clo_29761, &lam_29760, 26, env, 3,
            _29742, x_29744, _29745);
          instr_recv(&recv_struct_29762, _29745, 13);
          instr_call(&tmp_29763, clo_29761, recv_struct_29762);
          instr_free_clo(clo_29761);
          instr_mov(&case_29746, tmp_29763);
          break;
        case 24:
          instr_struct(&unit_struct_29764, 1, 0);
          instr_mov(&case_29746, unit_struct_29764);
          break;}
      instr_mov(&case_29743, case_29746);
      break;}
  return case_29743;
}

clc_ptr lam_29769(clc_ptr _29740, clc_env env)
{
  clc_ptr clo_29766; clc_ptr recv_struct_29767; clc_ptr tmp_29768;
  instr_clo(&clo_29766, &lam_29765, 24, env, 1, _29740);
  instr_recv(&recv_struct_29767, _29740, 13);
  instr_call(&tmp_29768, clo_29766, recv_struct_29767);
  instr_free_clo(clo_29766);
  return tmp_29768;
}

clc_ptr lam_29771(clc_ptr _29738, clc_env env)
{
  clc_ptr clo_29770;
  instr_clo(&clo_29770, &lam_29769, 22, env, 1, _29738);
  return clo_29770;
}

clc_ptr ref_handler_29773(clc_ptr A_29736, clc_env env)
{
  clc_ptr clo_29772;
  instr_clo(&clo_29772, &lam_29771, 20, env, 1, A_29736);
  return clo_29772;
}

clc_ptr fork_proc_29787(clc_env env)
{
  clc_ptr fork_final_29785; clc_ptr tmp_29782; clc_ptr tmp_29783;
  clc_ptr tmp_29784;
  instr_call(&tmp_29782, env[7], env[5]);
  instr_call(&tmp_29783, tmp_29782, env[3]);
  instr_call(&tmp_29784, tmp_29783, env[0]);
  instr_free_clo(tmp_29783);
  instr_mov(&fork_final_29785, tmp_29784);
  instr_free_thread(env);
  return fork_final_29785;
}

clc_ptr lam_29788(clc_ptr _29780, clc_env env)
{
  clc_ptr fork_res_29786;
  instr_open(&fork_res_29786, &fork_proc_29787, _29780, 25, env, 1,
    _29780);
  return fork_res_29786;
}

clc_ptr lam_29790(clc_ptr _29778, clc_env env)
{
  clc_ptr clo_29789;
  instr_clo(&clo_29789, &lam_29788, 23, env, 1, _29778);
  return clo_29789;
}

clc_ptr mk_ref_29792(clc_ptr A_29776, clc_env env)
{
  clc_ptr clo_29791;
  instr_clo(&clo_29791, &lam_29790, 21, env, 1, A_29776);
  return clo_29791;
}

clc_ptr lam_29805(clc_ptr _29799, clc_env env)
{
  clc_ptr SET_c23_29801; clc_ptr send_clo_29800; clc_ptr send_clo_29803;
  clc_ptr tmp_29802; clc_ptr tmp_29804;
  instr_send(&send_clo_29800, _29799);
  instr_struct(&SET_c23_29801, 23, 0);
  instr_call(&tmp_29802, send_clo_29800, SET_c23_29801);
  instr_free_clo(send_clo_29800);
  instr_send(&send_clo_29803, tmp_29802);
  instr_call(&tmp_29804, send_clo_29803, env[1]);
  instr_free_clo(send_clo_29803);
  return tmp_29804;
}

clc_ptr lam_29807(clc_ptr _29797, clc_env env)
{
  clc_ptr clo_29806;
  instr_clo(&clo_29806, &lam_29805, 24, env, 1, _29797);
  return clo_29806;
}

clc_ptr set_ref_29809(clc_ptr A_29795, clc_env env)
{
  clc_ptr clo_29808;
  instr_clo(&clo_29808, &lam_29807, 22, env, 1, A_29795);
  return clo_29808;
}

clc_ptr lam_29819(clc_ptr _29814, clc_env env)
{
  clc_ptr GET_c22_29816; clc_ptr recv_struct_29818; clc_ptr send_clo_29815;
  clc_ptr tmp_29817;
  instr_send(&send_clo_29815, _29814);
  instr_struct(&GET_c22_29816, 22, 0);
  instr_call(&tmp_29817, send_clo_29815, GET_c22_29816);
  instr_free_clo(send_clo_29815);
  instr_recv(&recv_struct_29818, tmp_29817, 13);
  return recv_struct_29818;
}

clc_ptr get_ref_29821(clc_ptr A_29812, clc_env env)
{
  clc_ptr clo_29820;
  instr_clo(&clo_29820, &lam_29819, 23, env, 1, A_29812);
  return clo_29820;
}

clc_ptr lam_29831(clc_ptr _29826, clc_env env)
{
  clc_ptr FREE_c24_29829; clc_ptr send_clo_29828; clc_ptr tmp_29830;
  clc_ptr unit_struct_29827;
  instr_send(&send_clo_29828, _29826);
  instr_struct(&FREE_c24_29829, 24, 0);
  instr_call(&tmp_29830, send_clo_29828, FREE_c24_29829);
  instr_free_clo(send_clo_29828);
  instr_close(&unit_struct_29827, tmp_29830);
  return unit_struct_29827;
}

clc_ptr free_ref_29833(clc_ptr A_29824, clc_env env)
{
  clc_ptr clo_29832;
  instr_clo(&clo_29832, &lam_29831, 24, env, 1, A_29824);
  return clo_29832;
}

clc_ptr lam_29886(clc_ptr _29884, clc_env env)
{
  clc_ptr case_29885;
  switch(((clc_node)_29884)->tag){
    case 1: instr_mov(&case_29885, env[21]);
            break;}
  return case_29885;
}

clc_ptr lam_29891(clc_ptr _29881, clc_env env)
{
  clc_ptr case_29882; clc_ptr clo_29887; clc_ptr tmp_29888;
  clc_ptr tmp_29889; clc_ptr tmp_29890;
  switch(((clc_node)_29881)->tag){
    case 1:
      instr_clo(&clo_29887, &lam_29886, 47, env, 1, _29881);
      instr_call(&tmp_29888, env[23], 0);
      instr_call(&tmp_29889, tmp_29888, env[4]);
      instr_free_clo(tmp_29888);
      instr_call(&tmp_29890, clo_29887, tmp_29889);
      instr_free_clo(clo_29887);
      instr_mov(&case_29882, tmp_29890);
      break;}
  return case_29882;
}

clc_ptr lam_29895(clc_ptr _29858, clc_env env)
{
  clc_ptr _29861; clc_ptr Ascii_c16_29875; clc_ptr EmptyString_c17_29876;
  clc_ptr String_c18_29877; clc_ptr case_29859; clc_ptr clo_29892;
  clc_ptr false_c3_29867; clc_ptr false_c3_29868; clc_ptr false_c3_29869;
  clc_ptr false_c3_29870; clc_ptr false_c3_29872; clc_ptr false_c3_29874;
  clc_ptr stdout_29862; clc_ptr tmp_29863; clc_ptr tmp_29864;
  clc_ptr tmp_29865; clc_ptr tmp_29866; clc_ptr tmp_29878; clc_ptr tmp_29879;
  clc_ptr tmp_29893; clc_ptr tmp_29894; clc_ptr true_c2_29871;
  clc_ptr true_c2_29873; clc_ptr x_29860;
  switch(((clc_node)_29858)->tag){
    case 13:
      instr_mov(&x_29860, ((clc_node)_29858)->data[0]);
      instr_mov(&_29861, ((clc_node)_29858)->data[1]);
      instr_free_struct(_29858);
      instr_call(&tmp_29863, env[27], env[17]);
      instr_call(&tmp_29864, env[38], env[9]);
      instr_call(&tmp_29865, tmp_29864, x_29860);
      instr_call(&tmp_29866, env[38], tmp_29865);
      instr_struct(&false_c3_29867, 3, 0);
      instr_struct(&false_c3_29868, 3, 0);
      instr_struct(&false_c3_29869, 3, 0);
      instr_struct(&false_c3_29870, 3, 0);
      instr_struct(&true_c2_29871, 2, 0);
      instr_struct(&false_c3_29872, 3, 0);
      instr_struct(&true_c2_29873, 2, 0);
      instr_struct(&false_c3_29874, 3, 0);
      instr_struct(&Ascii_c16_29875, 16, 8,
        false_c3_29867, false_c3_29868, false_c3_29869, false_c3_29870,
        true_c2_29871, false_c3_29872, true_c2_29873, false_c3_29874);
      instr_struct(&EmptyString_c17_29876, 17, 0);
      instr_struct(&String_c18_29877, 18, 2,
        Ascii_c16_29875, EmptyString_c17_29876);
      instr_call(&tmp_29878, tmp_29866, String_c18_29877);
      instr_call(&tmp_29879, tmp_29863, tmp_29878);
      instr_free_clo(tmp_29863);
      instr_mov(&stdout_29862, tmp_29879);
      instr_clo(&clo_29892, &lam_29891, 42, env, 4,
        stdout_29862, _29858, x_29860, _29861);
      instr_call(&tmp_29893, env[26], stdout_29862);
      instr_call(&tmp_29894, clo_29892, tmp_29893);
      instr_free_clo(clo_29892);
      instr_mov(&case_29859, tmp_29894);
      break;}
  return case_29859;
}

clc_ptr lam_29900(clc_ptr _29851, clc_env env)
{
  clc_ptr case_29852; clc_ptr clo_29896; clc_ptr ref_29853;
  clc_ptr tmp_29854; clc_ptr tmp_29855; clc_ptr tmp_29856; clc_ptr tmp_29897;
  clc_ptr tmp_29898; clc_ptr tmp_29899;
  switch(((clc_node)_29851)->tag){
    case 1:
      instr_call(&tmp_29854, env[17], 0);
      instr_call(&tmp_29855, tmp_29854, env[2]);
      instr_call(&tmp_29856, tmp_29855, env[7]);
      instr_free_clo(tmp_29855);
      instr_mov(&ref_29853, tmp_29856);
      instr_clo(&clo_29896, &lam_29895, 39, env, 2, ref_29853, _29851);
      instr_call(&tmp_29897, env[16], 0);
      instr_call(&tmp_29898, tmp_29897, ref_29853);
      instr_free_clo(tmp_29897);
      instr_call(&tmp_29899, clo_29896, tmp_29898);
      instr_free_clo(clo_29896);
      instr_mov(&case_29852, tmp_29899);
      break;}
  return case_29852;
}

clc_ptr lam_29904(clc_ptr _29846, clc_env env)
{
  clc_ptr _29849; clc_ptr case_29847; clc_ptr clo_29901; clc_ptr tmp_29902;
  clc_ptr tmp_29903; clc_ptr x_29848;
  switch(((clc_node)_29846)->tag){
    case 13:
      instr_mov(&x_29848, ((clc_node)_29846)->data[0]);
      instr_mov(&_29849, ((clc_node)_29846)->data[1]);
      instr_free_struct(_29846);
      instr_clo(&clo_29901, &lam_29900, 35, env, 3, _29846, x_29848, _29849);
      instr_call(&tmp_29902, env[21], _29849);
      instr_call(&tmp_29903, clo_29901, tmp_29902);
      instr_free_clo(clo_29901);
      instr_mov(&case_29847, tmp_29903);
      break;}
  return case_29847;
}

clc_ptr lam_29908(clc_ptr _29841, clc_env env)
{
  clc_ptr _29844; clc_ptr case_29842; clc_ptr clo_29905; clc_ptr tmp_29906;
  clc_ptr tmp_29907; clc_ptr x_29843;
  switch(((clc_node)_29841)->tag){
    case 13:
      instr_mov(&x_29843, ((clc_node)_29841)->data[0]);
      instr_mov(&_29844, ((clc_node)_29841)->data[1]);
      instr_free_struct(_29841);
      instr_clo(&clo_29905, &lam_29904, 31, env, 3, _29841, x_29843, _29844);
      instr_call(&tmp_29906, env[18], env[5]);
      instr_call(&tmp_29907, clo_29905, tmp_29906);
      instr_free_clo(clo_29905);
      instr_mov(&case_29842, tmp_29907);
      break;}
  return case_29842;
}

clc_ptr lam_29913(clc_ptr _29836, clc_env env)
{
  clc_ptr _29838; clc_ptr _29839; clc_ptr case_29837; clc_ptr clo_29909;
  clc_ptr tmp_29910; clc_ptr tmp_29911; clc_ptr tmp_29912;
  switch(((clc_node)_29836)->tag){
    case 14:
      instr_mov(&_29838, ((clc_node)_29836)->data[0]);
      instr_mov(&_29839, ((clc_node)_29836)->data[1]);
      instr_free_struct(_29836);
      instr_clo(&clo_29909, &lam_29908, 27, env, 3, _29836, _29838, _29839);
      instr_call(&tmp_29910, env[4], 0);
      instr_call(&tmp_29911, tmp_29910, _29838);
      instr_free_clo(tmp_29910);
      instr_call(&tmp_29912, clo_29909, tmp_29911);
      instr_free_clo(clo_29909);
      instr_mov(&case_29837, tmp_29912);
      break;}
  return case_29837;
}

int main()
{
  clc_ptr _180; clc_ptr Ascii_c16_29924; clc_ptr Ascii_c16_29933;
  clc_ptr Ascii_c16_29942; clc_ptr Ascii_c16_29951; clc_ptr Ascii_c16_29960;
  clc_ptr Ascii_c16_29969; clc_ptr EmptyString_c17_29970;
  clc_ptr String_c18_29971; clc_ptr String_c18_29972;
  clc_ptr String_c18_29973; clc_ptr String_c18_29974;
  clc_ptr String_c18_29975; clc_ptr String_c18_29976; clc_ptr addn_3;
  clc_ptr addn_29595; clc_ptr cat_67; clc_ptr cat_29633; clc_ptr clo_29914;
  clc_ptr close_err_130; clc_ptr close_err_29730; clc_ptr close_in_114;
  clc_ptr close_in_29688; clc_ptr close_out_122; clc_ptr close_out_29709;
  clc_ptr false_c3_29916; clc_ptr false_c3_29919; clc_ptr false_c3_29921;
  clc_ptr false_c3_29922; clc_ptr false_c3_29923; clc_ptr false_c3_29925;
  clc_ptr false_c3_29928; clc_ptr false_c3_29929; clc_ptr false_c3_29931;
  clc_ptr false_c3_29934; clc_ptr false_c3_29937; clc_ptr false_c3_29940;
  clc_ptr false_c3_29941; clc_ptr false_c3_29943; clc_ptr false_c3_29946;
  clc_ptr false_c3_29949; clc_ptr false_c3_29950; clc_ptr false_c3_29952;
  clc_ptr false_c3_29955; clc_ptr false_c3_29961; clc_ptr false_c3_29962;
  clc_ptr false_c3_29964; clc_ptr false_c3_29965; clc_ptr false_c3_29966;
  clc_ptr false_c3_29967; clc_ptr false_c3_29968; clc_ptr free_ref_173;
  clc_ptr free_ref_29834; clc_ptr get_ref_166; clc_ptr get_ref_29822;
  clc_ptr lt_84; clc_ptr lt_29651; clc_ptr mk_ref_151; clc_ptr mk_ref_29793;
  clc_ptr printerr_125; clc_ptr printerr_29722; clc_ptr printline_117;
  clc_ptr printline_29701; clc_ptr readline_109; clc_ptr readline_29680;
  clc_ptr ref_handler_139; clc_ptr ref_handler_29774; clc_ptr ref_t_133;
  clc_ptr ref_t_29734; clc_ptr set_ref_159; clc_ptr set_ref_29810;
  clc_ptr stderr_rec_102; clc_ptr stderr_rec_29666; clc_ptr stderr_t_108;
  clc_ptr stdin_179; clc_ptr stdin_rec_94; clc_ptr stdin_rec_29656;
  clc_ptr stdin_t_106; clc_ptr stdout_178; clc_ptr stdout_rec_98;
  clc_ptr stdout_rec_29661; clc_ptr stdout_t_107; clc_ptr strlen_74;
  clc_ptr strlen_29643; clc_ptr subn_9; clc_ptr subn_29615;
  clc_ptr tmp_29668; clc_ptr tmp_29670; clc_ptr tmp_29672; clc_ptr tmp_29915;
  clc_ptr tmp_29977; clc_ptr tmp_29978; clc_ptr tmp_29979;
  clc_ptr true_c2_29917; clc_ptr true_c2_29918; clc_ptr true_c2_29920;
  clc_ptr true_c2_29926; clc_ptr true_c2_29927; clc_ptr true_c2_29930;
  clc_ptr true_c2_29932; clc_ptr true_c2_29935; clc_ptr true_c2_29936;
  clc_ptr true_c2_29938; clc_ptr true_c2_29939; clc_ptr true_c2_29944;
  clc_ptr true_c2_29945; clc_ptr true_c2_29947; clc_ptr true_c2_29948;
  clc_ptr true_c2_29953; clc_ptr true_c2_29954; clc_ptr true_c2_29956;
  clc_ptr true_c2_29957; clc_ptr true_c2_29958; clc_ptr true_c2_29959;
  clc_ptr true_c2_29963; clc_ptr tt_c1_29667; clc_ptr tt_c1_29669;
  clc_ptr tt_c1_29671;
  clc_env env = 0;
  instr_init();
  instr_clo(&addn_29595, &addn_29594, 0, env, 1, 0);
  instr_mov(&addn_3, addn_29595);
  instr_clo(&subn_29615, &subn_29614, 0, env, 2, addn_3, 0);
  instr_mov(&subn_9, subn_29615);
  instr_clo(&cat_29633, &cat_29632, 0, env, 3, subn_9, addn_3, 0);
  instr_mov(&cat_67, cat_29633);
  instr_clo(&strlen_29643, &strlen_29642, 0, env, 4,
    cat_67, subn_9, addn_3, 0);
  instr_mov(&strlen_74, strlen_29643);
  instr_clo(&lt_29651, &lt_29650, 0, env, 5,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&lt_84, lt_29651);
  instr_clo(&stdin_rec_29656, &stdin_rec_29655, 0, env, 6,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdin_rec_94, stdin_rec_29656);
  instr_clo(&stdout_rec_29661, &stdout_rec_29660, 0, env, 7,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdout_rec_98, stdout_rec_29661);
  instr_clo(&stderr_rec_29666, &stderr_rec_29665, 0, env, 8,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stderr_rec_102, stderr_rec_29666);
  instr_struct(&tt_c1_29667, 1, 0);
  instr_call(&tmp_29668, stdin_rec_94, tt_c1_29667);
  instr_mov(&stdin_t_106, tmp_29668);
  instr_struct(&tt_c1_29669, 1, 0);
  instr_call(&tmp_29670, stdout_rec_98, tt_c1_29669);
  instr_mov(&stdout_t_107, tmp_29670);
  instr_struct(&tt_c1_29671, 1, 0);
  instr_call(&tmp_29672, stderr_rec_102, tt_c1_29671);
  instr_mov(&stderr_t_108, tmp_29672);
  instr_clo(&readline_29680, &readline_29679, 0, env, 12,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&readline_109, readline_29680);
  instr_clo(&close_in_29688, &close_in_29687, 0, env, 13,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_in_114, close_in_29688);
  instr_clo(&printline_29701, &printline_29700, 0, env, 14,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&printline_117, printline_29701);
  instr_clo(&close_out_29709, &close_out_29708, 0, env, 15,
    printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_out_122, close_out_29709);
  instr_clo(&printerr_29722, &printerr_29721, 0, env, 16,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&printerr_125, printerr_29722);
  instr_clo(&close_err_29730, &close_err_29729, 0, env, 17,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_err_130, close_err_29730);
  instr_clo(&ref_t_29734, &ref_t_29733, 0, env, 18,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&ref_t_133, ref_t_29734);
  instr_clo(&ref_handler_29774, &ref_handler_29773, 0, env, 19,
    ref_t_133, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&ref_handler_139, ref_handler_29774);
  instr_clo(&mk_ref_29793, &mk_ref_29792, 0, env, 20,
    ref_handler_139, ref_t_133, close_err_130, printerr_125, close_out_122,
    printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&mk_ref_151, mk_ref_29793);
  instr_clo(&set_ref_29810, &set_ref_29809, 0, env, 21,
    mk_ref_151, ref_handler_139, ref_t_133, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&set_ref_159, set_ref_29810);
  instr_clo(&get_ref_29822, &get_ref_29821, 0, env, 22,
    set_ref_159, mk_ref_151, ref_handler_139, ref_t_133, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&get_ref_166, get_ref_29822);
  instr_clo(&free_ref_29834, &free_ref_29833, 0, env, 23,
    get_ref_166, set_ref_159, mk_ref_151, ref_handler_139, ref_t_133,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&free_ref_173, free_ref_29834);
  instr_trg(&stdout_178, &proc_stdout);
  instr_trg(&stdin_179, &proc_stdin);
  instr_clo(&clo_29914, &lam_29913, 0, env, 26,
    stdin_179, stdout_178, free_ref_173, get_ref_166, set_ref_159,
    mk_ref_151, ref_handler_139, ref_t_133, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_call(&tmp_29915, mk_ref_151, 0);
  instr_struct(&false_c3_29916, 3, 0);
  instr_struct(&true_c2_29917, 2, 0);
  instr_struct(&true_c2_29918, 2, 0);
  instr_struct(&false_c3_29919, 3, 0);
  instr_struct(&true_c2_29920, 2, 0);
  instr_struct(&false_c3_29921, 3, 0);
  instr_struct(&false_c3_29922, 3, 0);
  instr_struct(&false_c3_29923, 3, 0);
  instr_struct(&Ascii_c16_29924, 16, 8,
    false_c3_29916, true_c2_29917, true_c2_29918, false_c3_29919,
    true_c2_29920, false_c3_29921, false_c3_29922, false_c3_29923);
  instr_struct(&false_c3_29925, 3, 0);
  instr_struct(&true_c2_29926, 2, 0);
  instr_struct(&true_c2_29927, 2, 0);
  instr_struct(&false_c3_29928, 3, 0);
  instr_struct(&false_c3_29929, 3, 0);
  instr_struct(&true_c2_29930, 2, 0);
  instr_struct(&false_c3_29931, 3, 0);
  instr_struct(&true_c2_29932, 2, 0);
  instr_struct(&Ascii_c16_29933, 16, 8,
    false_c3_29925, true_c2_29926, true_c2_29927, false_c3_29928,
    false_c3_29929, true_c2_29930, false_c3_29931, true_c2_29932);
  instr_struct(&false_c3_29934, 3, 0);
  instr_struct(&true_c2_29935, 2, 0);
  instr_struct(&true_c2_29936, 2, 0);
  instr_struct(&false_c3_29937, 3, 0);
  instr_struct(&true_c2_29938, 2, 0);
  instr_struct(&true_c2_29939, 2, 0);
  instr_struct(&false_c3_29940, 3, 0);
  instr_struct(&false_c3_29941, 3, 0);
  instr_struct(&Ascii_c16_29942, 16, 8,
    false_c3_29934, true_c2_29935, true_c2_29936, false_c3_29937,
    true_c2_29938, true_c2_29939, false_c3_29940, false_c3_29941);
  instr_struct(&false_c3_29943, 3, 0);
  instr_struct(&true_c2_29944, 2, 0);
  instr_struct(&true_c2_29945, 2, 0);
  instr_struct(&false_c3_29946, 3, 0);
  instr_struct(&true_c2_29947, 2, 0);
  instr_struct(&true_c2_29948, 2, 0);
  instr_struct(&false_c3_29949, 3, 0);
  instr_struct(&false_c3_29950, 3, 0);
  instr_struct(&Ascii_c16_29951, 16, 8,
    false_c3_29943, true_c2_29944, true_c2_29945, false_c3_29946,
    true_c2_29947, true_c2_29948, false_c3_29949, false_c3_29950);
  instr_struct(&false_c3_29952, 3, 0);
  instr_struct(&true_c2_29953, 2, 0);
  instr_struct(&true_c2_29954, 2, 0);
  instr_struct(&false_c3_29955, 3, 0);
  instr_struct(&true_c2_29956, 2, 0);
  instr_struct(&true_c2_29957, 2, 0);
  instr_struct(&true_c2_29958, 2, 0);
  instr_struct(&true_c2_29959, 2, 0);
  instr_struct(&Ascii_c16_29960, 16, 8,
    false_c3_29952, true_c2_29953, true_c2_29954, false_c3_29955,
    true_c2_29956, true_c2_29957, true_c2_29958, true_c2_29959);
  instr_struct(&false_c3_29961, 3, 0);
  instr_struct(&false_c3_29962, 3, 0);
  instr_struct(&true_c2_29963, 2, 0);
  instr_struct(&false_c3_29964, 3, 0);
  instr_struct(&false_c3_29965, 3, 0);
  instr_struct(&false_c3_29966, 3, 0);
  instr_struct(&false_c3_29967, 3, 0);
  instr_struct(&false_c3_29968, 3, 0);
  instr_struct(&Ascii_c16_29969, 16, 8,
    false_c3_29961, false_c3_29962, true_c2_29963, false_c3_29964,
    false_c3_29965, false_c3_29966, false_c3_29967, false_c3_29968);
  instr_struct(&EmptyString_c17_29970, 17, 0);
  instr_struct(&String_c18_29971, 18, 2,
    Ascii_c16_29969, EmptyString_c17_29970);
  instr_struct(&String_c18_29972, 18, 2,
    Ascii_c16_29960, String_c18_29971);
  instr_struct(&String_c18_29973, 18, 2,
    Ascii_c16_29951, String_c18_29972);
  instr_struct(&String_c18_29974, 18, 2,
    Ascii_c16_29942, String_c18_29973);
  instr_struct(&String_c18_29975, 18, 2,
    Ascii_c16_29933, String_c18_29974);
  instr_struct(&String_c18_29976, 18, 2,
    Ascii_c16_29924, String_c18_29975);
  instr_call(&tmp_29977, tmp_29915, String_c18_29976);
  instr_call(&tmp_29978, tmp_29977, 0);
  instr_call(&tmp_29979, clo_29914, tmp_29978);
  instr_free_clo(clo_29914);
  instr_mov(&_180, tmp_29979);
  return 0;
}
