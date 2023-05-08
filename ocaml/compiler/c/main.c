#include "runtime.h"

clc_ptr lam_29774(clc_ptr _29773, clc_env env)
{
  
  
  return _29773;
}

clc_ptr lam_29782(clc_ptr _29778, clc_env env)
{
  clc_ptr succ_c5_29781; clc_ptr tmp_29779; clc_ptr tmp_29780;
  instr_call(&tmp_29779, env[3], env[2]);
  instr_call(&tmp_29780, tmp_29779, _29778);
  instr_struct(&succ_c5_29781, 5, 1,
    tmp_29780);
  return succ_c5_29781;
}

clc_ptr addn_29784(clc_ptr _29770, clc_env env)
{
  clc_ptr _29776; clc_ptr case_29771; clc_ptr clo_29775; clc_ptr clo_29783;
  switch(((clc_node)_29770)->tag){
    case 4:
      instr_clo(&clo_29775, &lam_29774, 2, env, 1, _29770);
      instr_mov(&case_29771, clo_29775);
      break;
    case 5:
      instr_mov(&_29776, ((clc_node)_29770)->data[0]);
      instr_clo(&clo_29783, &lam_29782, 2, env, 2, _29770, _29776);
      instr_mov(&case_29771, clo_29783);
      break;}
  return case_29771;
}

clc_ptr lam_29792(clc_ptr _29790, clc_env env)
{
  clc_ptr zero_c4_29791;
  instr_struct(&zero_c4_29791, 4, 0);
  return zero_c4_29791;
}

clc_ptr lam_29802(clc_ptr _29796, clc_env env)
{
  clc_ptr _29799; clc_ptr case_29797; clc_ptr succ_c5_29798;
  clc_ptr tmp_29800; clc_ptr tmp_29801;
  switch(((clc_node)_29796)->tag){
    case 4:
      instr_struct(&succ_c5_29798, 5, 1,
        env[2]);
      instr_mov(&case_29797, succ_c5_29798);
      break;
    case 5:
      instr_mov(&_29799, ((clc_node)_29796)->data[0]);
      instr_call(&tmp_29800, env[3], env[2]);
      instr_call(&tmp_29801, tmp_29800, _29799);
      instr_mov(&case_29797, tmp_29801);
      break;}
  return case_29797;
}

clc_ptr subn_29804(clc_ptr _29787, clc_env env)
{
  clc_ptr _29794; clc_ptr case_29788; clc_ptr clo_29793; clc_ptr clo_29803;
  switch(((clc_node)_29787)->tag){
    case 4:
      instr_clo(&clo_29793, &lam_29792, 3, env, 1, _29787);
      instr_mov(&case_29788, clo_29793);
      break;
    case 5:
      instr_mov(&_29794, ((clc_node)_29787)->data[0]);
      instr_clo(&clo_29803, &lam_29802, 3, env, 2, _29787, _29794);
      instr_mov(&case_29788, clo_29803);
      break;}
  return case_29788;
}

clc_ptr lam_29811(clc_ptr _29810, clc_env env)
{
  
  
  return _29810;
}

clc_ptr lam_29820(clc_ptr _29816, clc_env env)
{
  clc_ptr String_c18_29819; clc_ptr tmp_29817; clc_ptr tmp_29818;
  instr_call(&tmp_29817, env[4], env[3]);
  instr_call(&tmp_29818, tmp_29817, _29816);
  instr_struct(&String_c18_29819, 18, 2,
    env[2], tmp_29818);
  return String_c18_29819;
}

clc_ptr cat_29822(clc_ptr _29807, clc_env env)
{
  clc_ptr _29813; clc_ptr _29814; clc_ptr case_29808; clc_ptr clo_29812;
  clc_ptr clo_29821;
  switch(((clc_node)_29807)->tag){
    case 17:
      instr_clo(&clo_29812, &lam_29811, 4, env, 1, _29807);
      instr_mov(&case_29808, clo_29812);
      break;
    case 18:
      instr_mov(&_29813, ((clc_node)_29807)->data[0]);
      instr_mov(&_29814, ((clc_node)_29807)->data[1]);
      instr_clo(&clo_29821, &lam_29820, 4, env, 3, _29807, _29813, _29814);
      instr_mov(&case_29808, clo_29821);
      break;}
  return case_29808;
}

clc_ptr strlen_29832(clc_ptr _29825, clc_env env)
{
  clc_ptr _29828; clc_ptr _29829; clc_ptr case_29826; clc_ptr succ_c5_29831;
  clc_ptr tmp_29830; clc_ptr zero_c4_29827;
  switch(((clc_node)_29825)->tag){
    case 17:
      instr_struct(&zero_c4_29827, 4, 0);
      instr_mov(&case_29826, zero_c4_29827);
      break;
    case 18:
      instr_mov(&_29828, ((clc_node)_29825)->data[0]);
      instr_mov(&_29829, ((clc_node)_29825)->data[1]);
      instr_call(&tmp_29830, env[0], _29829);
      instr_struct(&succ_c5_29831, 5, 1,
        tmp_29830);
      instr_mov(&case_29826, succ_c5_29831);
      break;}
  return case_29826;
}

clc_ptr lam_29838(clc_ptr _29837, clc_env env)
{
  
  
  return 0;
}

clc_ptr lt_29840(clc_ptr _29835, clc_env env)
{
  clc_ptr clo_29839;
  instr_clo(&clo_29839, &lam_29838, 6, env, 1, _29835);
  return clo_29839;
}

clc_ptr stdin_rec_29845(clc_ptr _29843, clc_env env)
{
  clc_ptr case_29844;
  switch(((clc_node)_29843)->tag){
    case 1: instr_mov(&case_29844, 0);
            break;}
  return case_29844;
}

clc_ptr stdout_rec_29850(clc_ptr _29848, clc_env env)
{
  clc_ptr case_29849;
  switch(((clc_node)_29848)->tag){
    case 1: instr_mov(&case_29849, 0);
            break;}
  return case_29849;
}

clc_ptr stderr_rec_29855(clc_ptr _29853, clc_env env)
{
  clc_ptr case_29854;
  switch(((clc_node)_29853)->tag){
    case 1: instr_mov(&case_29854, 0);
            break;}
  return case_29854;
}

clc_ptr readline_29869(clc_ptr _29864, clc_env env)
{
  clc_ptr recv_struct_29868; clc_ptr send_clo_29865; clc_ptr tmp_29867;
  clc_ptr true_c2_29866;
  instr_send(&send_clo_29865, _29864);
  instr_struct(&true_c2_29866, 2, 0);
  instr_call(&tmp_29867, send_clo_29865, true_c2_29866);
  instr_free_clo(send_clo_29865);
  instr_recv(&recv_struct_29868, tmp_29867, 13);
  return recv_struct_29868;
}

clc_ptr close_in_29877(clc_ptr _29872, clc_env env)
{
  clc_ptr false_c3_29875; clc_ptr send_clo_29874; clc_ptr tmp_29876;
  clc_ptr unit_struct_29873;
  instr_send(&send_clo_29874, _29872);
  instr_struct(&false_c3_29875, 3, 0);
  instr_call(&tmp_29876, send_clo_29874, false_c3_29875);
  instr_free_clo(send_clo_29874);
  instr_struct(&unit_struct_29873, 1, 0);
  return unit_struct_29873;
}

clc_ptr lam_29888(clc_ptr _29882, clc_env env)
{
  clc_ptr send_clo_29883; clc_ptr send_clo_29886; clc_ptr tmp_29885;
  clc_ptr tmp_29887; clc_ptr true_c2_29884;
  instr_send(&send_clo_29883, env[1]);
  instr_struct(&true_c2_29884, 2, 0);
  instr_call(&tmp_29885, send_clo_29883, true_c2_29884);
  instr_free_clo(send_clo_29883);
  instr_send(&send_clo_29886, tmp_29885);
  instr_call(&tmp_29887, send_clo_29886, _29882);
  instr_free_clo(send_clo_29886);
  return tmp_29887;
}

clc_ptr printline_29890(clc_ptr _29880, clc_env env)
{
  clc_ptr clo_29889;
  instr_clo(&clo_29889, &lam_29888, 15, env, 1, _29880);
  return clo_29889;
}

clc_ptr close_out_29898(clc_ptr _29893, clc_env env)
{
  clc_ptr false_c3_29896; clc_ptr send_clo_29895; clc_ptr tmp_29897;
  clc_ptr unit_struct_29894;
  instr_send(&send_clo_29895, _29893);
  instr_struct(&false_c3_29896, 3, 0);
  instr_call(&tmp_29897, send_clo_29895, false_c3_29896);
  instr_free_clo(send_clo_29895);
  instr_struct(&unit_struct_29894, 1, 0);
  return unit_struct_29894;
}

clc_ptr lam_29909(clc_ptr _29903, clc_env env)
{
  clc_ptr send_clo_29904; clc_ptr send_clo_29907; clc_ptr tmp_29906;
  clc_ptr tmp_29908; clc_ptr true_c2_29905;
  instr_send(&send_clo_29904, env[1]);
  instr_struct(&true_c2_29905, 2, 0);
  instr_call(&tmp_29906, send_clo_29904, true_c2_29905);
  instr_free_clo(send_clo_29904);
  instr_send(&send_clo_29907, tmp_29906);
  instr_call(&tmp_29908, send_clo_29907, _29903);
  instr_free_clo(send_clo_29907);
  return tmp_29908;
}

clc_ptr printerr_29911(clc_ptr _29901, clc_env env)
{
  clc_ptr clo_29910;
  instr_clo(&clo_29910, &lam_29909, 17, env, 1, _29901);
  return clo_29910;
}

clc_ptr close_err_29919(clc_ptr _29914, clc_env env)
{
  clc_ptr false_c3_29917; clc_ptr send_clo_29916; clc_ptr tmp_29918;
  clc_ptr unit_struct_29915;
  instr_send(&send_clo_29916, _29914);
  instr_struct(&false_c3_29917, 3, 0);
  instr_call(&tmp_29918, send_clo_29916, false_c3_29917);
  instr_free_clo(send_clo_29916);
  instr_struct(&unit_struct_29915, 1, 0);
  return unit_struct_29915;
}

clc_ptr ref_t_29923(clc_ptr _29922, clc_env env)
{
  
  
  return 0;
}

clc_ptr lam_29950(clc_ptr _29943, clc_env env)
{
  clc_ptr _29946; clc_ptr case_29944; clc_ptr tmp_29947; clc_ptr tmp_29948;
  clc_ptr tmp_29949; clc_ptr x_29945;
  switch(((clc_node)_29943)->tag){
    case 13:
      instr_mov(&x_29945, ((clc_node)_29943)->data[0]);
      instr_mov(&_29946, ((clc_node)_29943)->data[1]);
      instr_free_struct(_29943);
      instr_call(&tmp_29947, env[10], env[9]);
      instr_call(&tmp_29948, tmp_29947, x_29945);
      instr_call(&tmp_29949, tmp_29948, _29946);
      instr_free_clo(tmp_29948);
      instr_mov(&case_29944, tmp_29949);
      break;}
  return case_29944;
}

clc_ptr lam_29955(clc_ptr _29932, clc_env env)
{
  clc_ptr _29935; clc_ptr case_29933; clc_ptr case_29936; clc_ptr clo_29951;
  clc_ptr recv_struct_29952; clc_ptr send_clo_29939; clc_ptr tmp_29937;
  clc_ptr tmp_29938; clc_ptr tmp_29940; clc_ptr tmp_29941; clc_ptr tmp_29953;
  clc_ptr unit_struct_29954; clc_ptr x_29934;
  switch(((clc_node)_29932)->tag){
    case 13:
      instr_mov(&x_29934, ((clc_node)_29932)->data[0]);
      instr_mov(&_29935, ((clc_node)_29932)->data[1]);
      instr_free_struct(_29932);
      switch(((clc_node)x_29934)->tag){
        case 22:
          instr_call(&tmp_29937, env[6], env[5]);
          instr_call(&tmp_29938, tmp_29937, env[3]);
          instr_send(&send_clo_29939, _29935);
          instr_call(&tmp_29940, send_clo_29939, env[3]);
          instr_free_clo(send_clo_29939);
          instr_call(&tmp_29941, tmp_29938, tmp_29940);
          instr_free_clo(tmp_29938);
          instr_mov(&case_29936, tmp_29941);
          break;
        case 23:
          instr_clo(&clo_29951, &lam_29950, 26, env, 3,
            _29932, x_29934, _29935);
          instr_recv(&recv_struct_29952, _29935, 13);
          instr_call(&tmp_29953, clo_29951, recv_struct_29952);
          instr_free_clo(clo_29951);
          instr_mov(&case_29936, tmp_29953);
          break;
        case 24:
          instr_struct(&unit_struct_29954, 1, 0);
          instr_mov(&case_29936, unit_struct_29954);
          break;}
      instr_mov(&case_29933, case_29936);
      break;}
  return case_29933;
}

clc_ptr lam_29959(clc_ptr _29930, clc_env env)
{
  clc_ptr clo_29956; clc_ptr recv_struct_29957; clc_ptr tmp_29958;
  instr_clo(&clo_29956, &lam_29955, 24, env, 1, _29930);
  instr_recv(&recv_struct_29957, _29930, 13);
  instr_call(&tmp_29958, clo_29956, recv_struct_29957);
  instr_free_clo(clo_29956);
  return tmp_29958;
}

clc_ptr lam_29961(clc_ptr _29928, clc_env env)
{
  clc_ptr clo_29960;
  instr_clo(&clo_29960, &lam_29959, 22, env, 1, _29928);
  return clo_29960;
}

clc_ptr ref_handler_29963(clc_ptr A_29926, clc_env env)
{
  clc_ptr clo_29962;
  instr_clo(&clo_29962, &lam_29961, 20, env, 1, A_29926);
  return clo_29962;
}

clc_ptr fork_proc_29977(clc_env env)
{
  clc_ptr fork_final_29975; clc_ptr tmp_29972; clc_ptr tmp_29973;
  clc_ptr tmp_29974;
  instr_call(&tmp_29972, env[7], env[5]);
  instr_call(&tmp_29973, tmp_29972, env[3]);
  instr_call(&tmp_29974, tmp_29973, env[0]);
  instr_free_clo(tmp_29973);
  instr_mov(&fork_final_29975, tmp_29974);
  instr_free_thread(env);
  return fork_final_29975;
}

clc_ptr lam_29978(clc_ptr _29970, clc_env env)
{
  clc_ptr fork_res_29976;
  instr_open(&fork_res_29976, &fork_proc_29977, _29970, 25, env, 1,
    _29970);
  return fork_res_29976;
}

clc_ptr lam_29980(clc_ptr _29968, clc_env env)
{
  clc_ptr clo_29979;
  instr_clo(&clo_29979, &lam_29978, 23, env, 1, _29968);
  return clo_29979;
}

clc_ptr mk_ref_29982(clc_ptr A_29966, clc_env env)
{
  clc_ptr clo_29981;
  instr_clo(&clo_29981, &lam_29980, 21, env, 1, A_29966);
  return clo_29981;
}

clc_ptr lam_29995(clc_ptr _29989, clc_env env)
{
  clc_ptr SET_c23_29991; clc_ptr send_clo_29990; clc_ptr send_clo_29993;
  clc_ptr tmp_29992; clc_ptr tmp_29994;
  instr_send(&send_clo_29990, _29989);
  instr_struct(&SET_c23_29991, 23, 0);
  instr_call(&tmp_29992, send_clo_29990, SET_c23_29991);
  instr_free_clo(send_clo_29990);
  instr_send(&send_clo_29993, tmp_29992);
  instr_call(&tmp_29994, send_clo_29993, env[1]);
  instr_free_clo(send_clo_29993);
  return tmp_29994;
}

clc_ptr lam_29997(clc_ptr _29987, clc_env env)
{
  clc_ptr clo_29996;
  instr_clo(&clo_29996, &lam_29995, 24, env, 1, _29987);
  return clo_29996;
}

clc_ptr set_ref_29999(clc_ptr A_29985, clc_env env)
{
  clc_ptr clo_29998;
  instr_clo(&clo_29998, &lam_29997, 22, env, 1, A_29985);
  return clo_29998;
}

clc_ptr lam_30009(clc_ptr _30004, clc_env env)
{
  clc_ptr GET_c22_30006; clc_ptr recv_struct_30008; clc_ptr send_clo_30005;
  clc_ptr tmp_30007;
  instr_send(&send_clo_30005, _30004);
  instr_struct(&GET_c22_30006, 22, 0);
  instr_call(&tmp_30007, send_clo_30005, GET_c22_30006);
  instr_free_clo(send_clo_30005);
  instr_recv(&recv_struct_30008, tmp_30007, 13);
  return recv_struct_30008;
}

clc_ptr get_ref_30011(clc_ptr A_30002, clc_env env)
{
  clc_ptr clo_30010;
  instr_clo(&clo_30010, &lam_30009, 23, env, 1, A_30002);
  return clo_30010;
}

clc_ptr lam_30021(clc_ptr _30016, clc_env env)
{
  clc_ptr FREE_c24_30019; clc_ptr send_clo_30018; clc_ptr tmp_30020;
  clc_ptr unit_struct_30017;
  instr_send(&send_clo_30018, _30016);
  instr_struct(&FREE_c24_30019, 24, 0);
  instr_call(&tmp_30020, send_clo_30018, FREE_c24_30019);
  instr_free_clo(send_clo_30018);
  instr_close(&unit_struct_30017, tmp_30020);
  return unit_struct_30017;
}

clc_ptr free_ref_30023(clc_ptr A_30014, clc_env env)
{
  clc_ptr clo_30022;
  instr_clo(&clo_30022, &lam_30021, 24, env, 1, A_30014);
  return clo_30022;
}

clc_ptr lam_30076(clc_ptr _30074, clc_env env)
{
  clc_ptr case_30075;
  switch(((clc_node)_30074)->tag){
    case 1: instr_mov(&case_30075, env[21]);
            break;}
  return case_30075;
}

clc_ptr lam_30081(clc_ptr _30071, clc_env env)
{
  clc_ptr case_30072; clc_ptr clo_30077; clc_ptr tmp_30078;
  clc_ptr tmp_30079; clc_ptr tmp_30080;
  switch(((clc_node)_30071)->tag){
    case 1:
      instr_clo(&clo_30077, &lam_30076, 47, env, 1, _30071);
      instr_call(&tmp_30078, env[23], 0);
      instr_call(&tmp_30079, tmp_30078, env[4]);
      instr_free_clo(tmp_30078);
      instr_call(&tmp_30080, clo_30077, tmp_30079);
      instr_free_clo(clo_30077);
      instr_mov(&case_30072, tmp_30080);
      break;}
  return case_30072;
}

clc_ptr lam_30085(clc_ptr _30048, clc_env env)
{
  clc_ptr _30051; clc_ptr Ascii_c16_30065; clc_ptr EmptyString_c17_30066;
  clc_ptr String_c18_30067; clc_ptr case_30049; clc_ptr clo_30082;
  clc_ptr false_c3_30057; clc_ptr false_c3_30058; clc_ptr false_c3_30059;
  clc_ptr false_c3_30060; clc_ptr false_c3_30062; clc_ptr false_c3_30064;
  clc_ptr stdout_30052; clc_ptr tmp_30053; clc_ptr tmp_30054;
  clc_ptr tmp_30055; clc_ptr tmp_30056; clc_ptr tmp_30068; clc_ptr tmp_30069;
  clc_ptr tmp_30083; clc_ptr tmp_30084; clc_ptr true_c2_30061;
  clc_ptr true_c2_30063; clc_ptr x_30050;
  switch(((clc_node)_30048)->tag){
    case 13:
      instr_mov(&x_30050, ((clc_node)_30048)->data[0]);
      instr_mov(&_30051, ((clc_node)_30048)->data[1]);
      instr_free_struct(_30048);
      instr_call(&tmp_30053, env[27], env[17]);
      instr_call(&tmp_30054, env[38], env[9]);
      instr_call(&tmp_30055, tmp_30054, x_30050);
      instr_call(&tmp_30056, env[38], tmp_30055);
      instr_struct(&false_c3_30057, 3, 0);
      instr_struct(&false_c3_30058, 3, 0);
      instr_struct(&false_c3_30059, 3, 0);
      instr_struct(&false_c3_30060, 3, 0);
      instr_struct(&true_c2_30061, 2, 0);
      instr_struct(&false_c3_30062, 3, 0);
      instr_struct(&true_c2_30063, 2, 0);
      instr_struct(&false_c3_30064, 3, 0);
      instr_struct(&Ascii_c16_30065, 16, 8,
        false_c3_30057, false_c3_30058, false_c3_30059, false_c3_30060,
        true_c2_30061, false_c3_30062, true_c2_30063, false_c3_30064);
      instr_struct(&EmptyString_c17_30066, 17, 0);
      instr_struct(&String_c18_30067, 18, 2,
        Ascii_c16_30065, EmptyString_c17_30066);
      instr_call(&tmp_30068, tmp_30056, String_c18_30067);
      instr_call(&tmp_30069, tmp_30053, tmp_30068);
      instr_free_clo(tmp_30053);
      instr_mov(&stdout_30052, tmp_30069);
      instr_clo(&clo_30082, &lam_30081, 42, env, 4,
        stdout_30052, _30048, x_30050, _30051);
      instr_call(&tmp_30083, env[26], stdout_30052);
      instr_call(&tmp_30084, clo_30082, tmp_30083);
      instr_free_clo(clo_30082);
      instr_mov(&case_30049, tmp_30084);
      break;}
  return case_30049;
}

clc_ptr lam_30090(clc_ptr _30041, clc_env env)
{
  clc_ptr case_30042; clc_ptr clo_30086; clc_ptr ref_30043;
  clc_ptr tmp_30044; clc_ptr tmp_30045; clc_ptr tmp_30046; clc_ptr tmp_30087;
  clc_ptr tmp_30088; clc_ptr tmp_30089;
  switch(((clc_node)_30041)->tag){
    case 1:
      instr_call(&tmp_30044, env[17], 0);
      instr_call(&tmp_30045, tmp_30044, env[2]);
      instr_call(&tmp_30046, tmp_30045, env[7]);
      instr_free_clo(tmp_30045);
      instr_mov(&ref_30043, tmp_30046);
      instr_clo(&clo_30086, &lam_30085, 39, env, 2, ref_30043, _30041);
      instr_call(&tmp_30087, env[16], 0);
      instr_call(&tmp_30088, tmp_30087, ref_30043);
      instr_free_clo(tmp_30087);
      instr_call(&tmp_30089, clo_30086, tmp_30088);
      instr_free_clo(clo_30086);
      instr_mov(&case_30042, tmp_30089);
      break;}
  return case_30042;
}

clc_ptr lam_30094(clc_ptr _30036, clc_env env)
{
  clc_ptr _30039; clc_ptr case_30037; clc_ptr clo_30091; clc_ptr tmp_30092;
  clc_ptr tmp_30093; clc_ptr x_30038;
  switch(((clc_node)_30036)->tag){
    case 13:
      instr_mov(&x_30038, ((clc_node)_30036)->data[0]);
      instr_mov(&_30039, ((clc_node)_30036)->data[1]);
      instr_free_struct(_30036);
      instr_clo(&clo_30091, &lam_30090, 35, env, 3, _30036, x_30038, _30039);
      instr_call(&tmp_30092, env[21], _30039);
      instr_call(&tmp_30093, clo_30091, tmp_30092);
      instr_free_clo(clo_30091);
      instr_mov(&case_30037, tmp_30093);
      break;}
  return case_30037;
}

clc_ptr lam_30098(clc_ptr _30031, clc_env env)
{
  clc_ptr _30034; clc_ptr case_30032; clc_ptr clo_30095; clc_ptr tmp_30096;
  clc_ptr tmp_30097; clc_ptr x_30033;
  switch(((clc_node)_30031)->tag){
    case 13:
      instr_mov(&x_30033, ((clc_node)_30031)->data[0]);
      instr_mov(&_30034, ((clc_node)_30031)->data[1]);
      instr_free_struct(_30031);
      instr_clo(&clo_30095, &lam_30094, 31, env, 3, _30031, x_30033, _30034);
      instr_call(&tmp_30096, env[18], env[5]);
      instr_call(&tmp_30097, clo_30095, tmp_30096);
      instr_free_clo(clo_30095);
      instr_mov(&case_30032, tmp_30097);
      break;}
  return case_30032;
}

clc_ptr lam_30103(clc_ptr _30026, clc_env env)
{
  clc_ptr _30028; clc_ptr _30029; clc_ptr case_30027; clc_ptr clo_30099;
  clc_ptr tmp_30100; clc_ptr tmp_30101; clc_ptr tmp_30102;
  switch(((clc_node)_30026)->tag){
    case 14:
      instr_mov(&_30028, ((clc_node)_30026)->data[0]);
      instr_mov(&_30029, ((clc_node)_30026)->data[1]);
      instr_free_struct(_30026);
      instr_clo(&clo_30099, &lam_30098, 27, env, 3, _30026, _30028, _30029);
      instr_call(&tmp_30100, env[4], 0);
      instr_call(&tmp_30101, tmp_30100, _30028);
      instr_free_clo(tmp_30100);
      instr_call(&tmp_30102, clo_30099, tmp_30101);
      instr_free_clo(clo_30099);
      instr_mov(&case_30027, tmp_30102);
      break;}
  return case_30027;
}

int main()
{
  clc_ptr _180; clc_ptr Ascii_c16_30114; clc_ptr Ascii_c16_30123;
  clc_ptr Ascii_c16_30132; clc_ptr Ascii_c16_30141; clc_ptr Ascii_c16_30150;
  clc_ptr Ascii_c16_30159; clc_ptr EmptyString_c17_30160;
  clc_ptr String_c18_30161; clc_ptr String_c18_30162;
  clc_ptr String_c18_30163; clc_ptr String_c18_30164;
  clc_ptr String_c18_30165; clc_ptr String_c18_30166; clc_ptr addn_3;
  clc_ptr addn_29785; clc_ptr cat_67; clc_ptr cat_29823; clc_ptr clo_30104;
  clc_ptr close_err_130; clc_ptr close_err_29920; clc_ptr close_in_114;
  clc_ptr close_in_29878; clc_ptr close_out_122; clc_ptr close_out_29899;
  clc_ptr false_c3_30106; clc_ptr false_c3_30109; clc_ptr false_c3_30111;
  clc_ptr false_c3_30112; clc_ptr false_c3_30113; clc_ptr false_c3_30115;
  clc_ptr false_c3_30118; clc_ptr false_c3_30119; clc_ptr false_c3_30121;
  clc_ptr false_c3_30124; clc_ptr false_c3_30127; clc_ptr false_c3_30130;
  clc_ptr false_c3_30131; clc_ptr false_c3_30133; clc_ptr false_c3_30136;
  clc_ptr false_c3_30139; clc_ptr false_c3_30140; clc_ptr false_c3_30142;
  clc_ptr false_c3_30145; clc_ptr false_c3_30151; clc_ptr false_c3_30152;
  clc_ptr false_c3_30154; clc_ptr false_c3_30155; clc_ptr false_c3_30156;
  clc_ptr false_c3_30157; clc_ptr false_c3_30158; clc_ptr free_ref_173;
  clc_ptr free_ref_30024; clc_ptr get_ref_166; clc_ptr get_ref_30012;
  clc_ptr lt_84; clc_ptr lt_29841; clc_ptr mk_ref_151; clc_ptr mk_ref_29983;
  clc_ptr printerr_125; clc_ptr printerr_29912; clc_ptr printline_117;
  clc_ptr printline_29891; clc_ptr readline_109; clc_ptr readline_29870;
  clc_ptr ref_handler_139; clc_ptr ref_handler_29964; clc_ptr ref_t_133;
  clc_ptr ref_t_29924; clc_ptr set_ref_159; clc_ptr set_ref_30000;
  clc_ptr stderr_rec_102; clc_ptr stderr_rec_29856; clc_ptr stderr_t_108;
  clc_ptr stdin_179; clc_ptr stdin_rec_94; clc_ptr stdin_rec_29846;
  clc_ptr stdin_t_106; clc_ptr stdout_178; clc_ptr stdout_rec_98;
  clc_ptr stdout_rec_29851; clc_ptr stdout_t_107; clc_ptr strlen_74;
  clc_ptr strlen_29833; clc_ptr subn_9; clc_ptr subn_29805;
  clc_ptr tmp_29858; clc_ptr tmp_29860; clc_ptr tmp_29862; clc_ptr tmp_30105;
  clc_ptr tmp_30167; clc_ptr tmp_30168; clc_ptr tmp_30169;
  clc_ptr true_c2_30107; clc_ptr true_c2_30108; clc_ptr true_c2_30110;
  clc_ptr true_c2_30116; clc_ptr true_c2_30117; clc_ptr true_c2_30120;
  clc_ptr true_c2_30122; clc_ptr true_c2_30125; clc_ptr true_c2_30126;
  clc_ptr true_c2_30128; clc_ptr true_c2_30129; clc_ptr true_c2_30134;
  clc_ptr true_c2_30135; clc_ptr true_c2_30137; clc_ptr true_c2_30138;
  clc_ptr true_c2_30143; clc_ptr true_c2_30144; clc_ptr true_c2_30146;
  clc_ptr true_c2_30147; clc_ptr true_c2_30148; clc_ptr true_c2_30149;
  clc_ptr true_c2_30153; clc_ptr tt_c1_29857; clc_ptr tt_c1_29859;
  clc_ptr tt_c1_29861;
  clc_env env = 0;
  instr_init();
  instr_clo(&addn_29785, &addn_29784, 0, env, 1, 0);
  instr_mov(&addn_3, addn_29785);
  instr_clo(&subn_29805, &subn_29804, 0, env, 2, addn_3, 0);
  instr_mov(&subn_9, subn_29805);
  instr_clo(&cat_29823, &cat_29822, 0, env, 3, subn_9, addn_3, 0);
  instr_mov(&cat_67, cat_29823);
  instr_clo(&strlen_29833, &strlen_29832, 0, env, 4,
    cat_67, subn_9, addn_3, 0);
  instr_mov(&strlen_74, strlen_29833);
  instr_clo(&lt_29841, &lt_29840, 0, env, 5,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&lt_84, lt_29841);
  instr_clo(&stdin_rec_29846, &stdin_rec_29845, 0, env, 6,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdin_rec_94, stdin_rec_29846);
  instr_clo(&stdout_rec_29851, &stdout_rec_29850, 0, env, 7,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdout_rec_98, stdout_rec_29851);
  instr_clo(&stderr_rec_29856, &stderr_rec_29855, 0, env, 8,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stderr_rec_102, stderr_rec_29856);
  instr_struct(&tt_c1_29857, 1, 0);
  instr_call(&tmp_29858, stdin_rec_94, tt_c1_29857);
  instr_mov(&stdin_t_106, tmp_29858);
  instr_struct(&tt_c1_29859, 1, 0);
  instr_call(&tmp_29860, stdout_rec_98, tt_c1_29859);
  instr_mov(&stdout_t_107, tmp_29860);
  instr_struct(&tt_c1_29861, 1, 0);
  instr_call(&tmp_29862, stderr_rec_102, tt_c1_29861);
  instr_mov(&stderr_t_108, tmp_29862);
  instr_clo(&readline_29870, &readline_29869, 0, env, 12,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&readline_109, readline_29870);
  instr_clo(&close_in_29878, &close_in_29877, 0, env, 13,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_in_114, close_in_29878);
  instr_clo(&printline_29891, &printline_29890, 0, env, 14,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&printline_117, printline_29891);
  instr_clo(&close_out_29899, &close_out_29898, 0, env, 15,
    printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_out_122, close_out_29899);
  instr_clo(&printerr_29912, &printerr_29911, 0, env, 16,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&printerr_125, printerr_29912);
  instr_clo(&close_err_29920, &close_err_29919, 0, env, 17,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_err_130, close_err_29920);
  instr_clo(&ref_t_29924, &ref_t_29923, 0, env, 18,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&ref_t_133, ref_t_29924);
  instr_clo(&ref_handler_29964, &ref_handler_29963, 0, env, 19,
    ref_t_133, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&ref_handler_139, ref_handler_29964);
  instr_clo(&mk_ref_29983, &mk_ref_29982, 0, env, 20,
    ref_handler_139, ref_t_133, close_err_130, printerr_125, close_out_122,
    printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&mk_ref_151, mk_ref_29983);
  instr_clo(&set_ref_30000, &set_ref_29999, 0, env, 21,
    mk_ref_151, ref_handler_139, ref_t_133, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&set_ref_159, set_ref_30000);
  instr_clo(&get_ref_30012, &get_ref_30011, 0, env, 22,
    set_ref_159, mk_ref_151, ref_handler_139, ref_t_133, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&get_ref_166, get_ref_30012);
  instr_clo(&free_ref_30024, &free_ref_30023, 0, env, 23,
    get_ref_166, set_ref_159, mk_ref_151, ref_handler_139, ref_t_133,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&free_ref_173, free_ref_30024);
  instr_trg(&stdout_178, &proc_stdout);
  instr_trg(&stdin_179, &proc_stdin);
  instr_clo(&clo_30104, &lam_30103, 0, env, 26,
    stdin_179, stdout_178, free_ref_173, get_ref_166, set_ref_159,
    mk_ref_151, ref_handler_139, ref_t_133, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_call(&tmp_30105, mk_ref_151, 0);
  instr_struct(&false_c3_30106, 3, 0);
  instr_struct(&true_c2_30107, 2, 0);
  instr_struct(&true_c2_30108, 2, 0);
  instr_struct(&false_c3_30109, 3, 0);
  instr_struct(&true_c2_30110, 2, 0);
  instr_struct(&false_c3_30111, 3, 0);
  instr_struct(&false_c3_30112, 3, 0);
  instr_struct(&false_c3_30113, 3, 0);
  instr_struct(&Ascii_c16_30114, 16, 8,
    false_c3_30106, true_c2_30107, true_c2_30108, false_c3_30109,
    true_c2_30110, false_c3_30111, false_c3_30112, false_c3_30113);
  instr_struct(&false_c3_30115, 3, 0);
  instr_struct(&true_c2_30116, 2, 0);
  instr_struct(&true_c2_30117, 2, 0);
  instr_struct(&false_c3_30118, 3, 0);
  instr_struct(&false_c3_30119, 3, 0);
  instr_struct(&true_c2_30120, 2, 0);
  instr_struct(&false_c3_30121, 3, 0);
  instr_struct(&true_c2_30122, 2, 0);
  instr_struct(&Ascii_c16_30123, 16, 8,
    false_c3_30115, true_c2_30116, true_c2_30117, false_c3_30118,
    false_c3_30119, true_c2_30120, false_c3_30121, true_c2_30122);
  instr_struct(&false_c3_30124, 3, 0);
  instr_struct(&true_c2_30125, 2, 0);
  instr_struct(&true_c2_30126, 2, 0);
  instr_struct(&false_c3_30127, 3, 0);
  instr_struct(&true_c2_30128, 2, 0);
  instr_struct(&true_c2_30129, 2, 0);
  instr_struct(&false_c3_30130, 3, 0);
  instr_struct(&false_c3_30131, 3, 0);
  instr_struct(&Ascii_c16_30132, 16, 8,
    false_c3_30124, true_c2_30125, true_c2_30126, false_c3_30127,
    true_c2_30128, true_c2_30129, false_c3_30130, false_c3_30131);
  instr_struct(&false_c3_30133, 3, 0);
  instr_struct(&true_c2_30134, 2, 0);
  instr_struct(&true_c2_30135, 2, 0);
  instr_struct(&false_c3_30136, 3, 0);
  instr_struct(&true_c2_30137, 2, 0);
  instr_struct(&true_c2_30138, 2, 0);
  instr_struct(&false_c3_30139, 3, 0);
  instr_struct(&false_c3_30140, 3, 0);
  instr_struct(&Ascii_c16_30141, 16, 8,
    false_c3_30133, true_c2_30134, true_c2_30135, false_c3_30136,
    true_c2_30137, true_c2_30138, false_c3_30139, false_c3_30140);
  instr_struct(&false_c3_30142, 3, 0);
  instr_struct(&true_c2_30143, 2, 0);
  instr_struct(&true_c2_30144, 2, 0);
  instr_struct(&false_c3_30145, 3, 0);
  instr_struct(&true_c2_30146, 2, 0);
  instr_struct(&true_c2_30147, 2, 0);
  instr_struct(&true_c2_30148, 2, 0);
  instr_struct(&true_c2_30149, 2, 0);
  instr_struct(&Ascii_c16_30150, 16, 8,
    false_c3_30142, true_c2_30143, true_c2_30144, false_c3_30145,
    true_c2_30146, true_c2_30147, true_c2_30148, true_c2_30149);
  instr_struct(&false_c3_30151, 3, 0);
  instr_struct(&false_c3_30152, 3, 0);
  instr_struct(&true_c2_30153, 2, 0);
  instr_struct(&false_c3_30154, 3, 0);
  instr_struct(&false_c3_30155, 3, 0);
  instr_struct(&false_c3_30156, 3, 0);
  instr_struct(&false_c3_30157, 3, 0);
  instr_struct(&false_c3_30158, 3, 0);
  instr_struct(&Ascii_c16_30159, 16, 8,
    false_c3_30151, false_c3_30152, true_c2_30153, false_c3_30154,
    false_c3_30155, false_c3_30156, false_c3_30157, false_c3_30158);
  instr_struct(&EmptyString_c17_30160, 17, 0);
  instr_struct(&String_c18_30161, 18, 2,
    Ascii_c16_30159, EmptyString_c17_30160);
  instr_struct(&String_c18_30162, 18, 2,
    Ascii_c16_30150, String_c18_30161);
  instr_struct(&String_c18_30163, 18, 2,
    Ascii_c16_30141, String_c18_30162);
  instr_struct(&String_c18_30164, 18, 2,
    Ascii_c16_30132, String_c18_30163);
  instr_struct(&String_c18_30165, 18, 2,
    Ascii_c16_30123, String_c18_30164);
  instr_struct(&String_c18_30166, 18, 2,
    Ascii_c16_30114, String_c18_30165);
  instr_call(&tmp_30167, tmp_30105, String_c18_30166);
  instr_call(&tmp_30168, tmp_30167, 0);
  instr_call(&tmp_30169, clo_30104, tmp_30168);
  instr_free_clo(clo_30104);
  instr_mov(&_180, tmp_30169);
  return 0;
}
