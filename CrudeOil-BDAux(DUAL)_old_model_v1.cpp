#include <ilcplex/ilocplex.h>
#include <time.h>
#include <vector>
#include <sstream>
#include <string>

#include <iostream>
#include <fstream>

#include <algorithm>

#include <stdio.h>
#include <ilconcert/iloexpression.h>

#include <sys/stat.h>
#include <io.h>
#include <conio.h>
#include <process.h>
#include <direct.h>
#include <ctime>
#include <chrono>


//#include <iostream>
ILOSTLBEGIN

//-------------Global Variables--------------
int i, t, z, j, k, n, l;
const int imax = 3;
const int zmax = 12;
const int kmax = 5;
const int jmax = 3;
const int tmax = 4;
const int capmax = 100000;
const int capmin = 0;
const int BigM = 100000;
double E_it[imax][tmax];
double ae_ijt[imax][jmax][tmax];
double S_kt[kmax][tmax];
double as_kjt[kmax][jmax][tmax];
double initial_zj[zmax][jmax];

//Parameters affecting solution
double epsilon = 0.1;
double maxhours = 1;
double UpperBound = BigM;
double LowerBound = -BigM;
double UpperBoundGlobal = BigM;
double UpperBoundAux = BigM;
double UpperBoundGlobalAux = BigM;
double Gap = 1;
double fraction = 1;
long double duration;  // tracks time
int start = 0, BDFeasCuts = 0, BDOptCuts = 0, CutsPerIteration, NoOfMasterVars, NoOfSlaveVars, NoOfMasterCons, NoOfSlaveCons;
int BDFeasCutsFromAux = 0, BDFeasCutsFromFeasAux = 0, BDFeasCutsFromClass = 0;
int BDOptCutsFromAux = 0, BDOptCutsFromFeasAux = 0, BDOptCutsFromClass = 0;
int NoOfSameCuts = 0, NoOfSameMasterSolution = 0;

double CiztValue[imax][zmax][tmax];
double DkztValue[kmax][zmax][tmax];
double FzjtValue[zmax][jmax][tmax];
double SCiztValue[imax][zmax][tmax];
double SDkztValue[kmax][zmax][tmax];
double XizjtValue[imax][zmax][jmax][tmax];
double YzkjtValue[zmax][kmax][jmax][tmax];
double IzjtValue[zmax][jmax][tmax];
double ThetaValue = 0;

double OptimalCiztValue[imax][zmax][tmax];
double OptimalDkztValue[kmax][zmax][tmax];
double OptimalFzjtValue[zmax][jmax][tmax];
double OptimalSCiztValue[imax][zmax][tmax];
double OptimalSDkztValue[kmax][zmax][tmax];
double OptimalXizjtValue[imax][zmax][jmax][tmax];
double OptimalYzkjtValue[zmax][kmax][jmax][tmax];
double OptimalIzjtValue[zmax][jmax][tmax];
double OptimalThetaValue = 0;

double OptimalOriginalObjFunction = 0;
double OptimalMasterObjFunction = 0;
double OptimalPrimalSlaveObjFunction = 0;
double OptimalDualSlaveObjFunction = BigM;
double LowestDualSlaveObjFunction = BigM;
double LowestFeasAuxDualSlaveObjFunction = BigM;

ifstream infile;
ofstream outfile, solution, solution_results, solution1, solution_results1;
char* FilePath_DataSet = "C:/PhD_Examples/Data_CrudeOil";//C:/PhD_Examples //G:/Antonis/PhD_Examples
char* FilePath_Data = "C:/PhD_Examples/Data_CrudeOil";
char* FilePath_Results = "C:/PhD_Examples/Results_CrudeOil/BDAux(DUAL)_new";//G:/Antonis/PhD_Examples
//char* FilePath_Results_FileName = "BENDERS";
char FileName_DataSet[512] = "DataSet";
char FileName_DataSetIndices[512] = "DataSetIndices";
char FileName_Problem[512];


//--------Declare the environment of CPLEX----------------
IloEnv env;
//--------Construct models----------------
//IloModel modelSlave1 (env);
IloModel modelDualSlave(env);
IloModel modelDualSlaveAux(env);
IloModel modelDualSlaveFeasAux(env);
IloModel modelMaster(env);
//--------Construct Matrices----------------
typedef IloArray<IloNumArray> IloNumMatrix2x2;
typedef IloArray<IloNumMatrix2x2> IloNumMatrix3x3;
typedef IloArray<IloNumMatrix3x3> IloNumMatrix4x4;

typedef IloArray<IloNumVarArray> IloNumVarMatrix2x2;
typedef IloArray<IloNumVarMatrix2x2> IloNumVarMatrix3x3;
typedef IloArray<IloNumVarMatrix3x3> IloNumVarMatrix4x4;

typedef IloArray<IloRangeArray> IloRangeMatrix2x2;
typedef IloArray<IloRangeMatrix2x2> IloRangeMatrix3x3;
typedef IloArray<IloRangeMatrix3x3> IloRangeMatrix4x4;

//------Declare Decision Variables----------
IloNumVarMatrix3x3 Cizt(env, 0);
IloNumVarMatrix3x3 Dkzt(env, 0);
IloNumVarMatrix3x3 Fzjt(env, 0);
IloNumVarArray Zn(env, 0);


//------Declare Dual Decision Variables----------
IloNumVarMatrix3x3 U1_1ijt(env, 0);
IloNumVarMatrix3x3 U1_2ijt(env, 0);
IloNumVarMatrix3x3 U2_1kjt(env, 0);
IloNumVarMatrix3x3 U2_2kjt(env, 0);
IloNumVarMatrix3x3 U3_1zjt(env, 0);
IloNumVarMatrix3x3 U3_2zjt(env, 0);
IloNumVarMatrix2x2 U4zt(env, 0);
IloNumVarMatrix3x3 U5izt(env, 0);
IloNumVarMatrix3x3 U6izt(env, 0);
IloNumVarMatrix3x3 U7kzt(env, 0);
IloNumVarMatrix3x3 U8kzt(env, 0);
IloNumVarMatrix3x3 U9zjt(env, 0);
IloNumVarMatrix3x3 U10zjt(env, 0);
IloNumVarMatrix3x3 U11izt(env, 0);
IloNumVarMatrix3x3 U12kzt(env, 0);
IloNumVarMatrix3x3 U13izt(env, 0);
IloNumVarMatrix3x3 U14kzt(env, 0);

IloNumVarArray AllVars(env, 0);

//--------Declare Master constraints-------------
IloRangeMatrix2x2 CT3Melzt(env, 0);
IloRangeMatrix4x4 CT3C_ou_Dikzt(env, 0);
IloRangeMatrix2x2 SupFzj0(env, 0);
IloRangeMatrix2x2 SupCiz0(env, 0);
IloRangeMatrix2x2 SupDkz0(env, 0);
IloRangeMatrix2x2 Con3W1it(env, 0);
IloRangeMatrix2x2 Con5W2kt(env, 0);

//--------Declare Dual Slave constraints-------------
IloRangeMatrix4x4 Con1Xizjt(env, 0);
IloRangeMatrix4x4 Con2Yzkjt(env, 0);
IloRangeMatrix3x3 Con3Izjt(env, 0);
IloRangeMatrix3x3 Con4SCizt(env, 0);
IloRangeMatrix3x3 Con5SDkzt(env, 0);
IloRangeArray AuxConl(env, 0);
IloRangeMatrix3x3 Con4AuxSCizt(env, 0);
IloRangeMatrix3x3 Con5AuxSDkzt(env, 0);
IloRangeArray ExtraAuxConl(env, 0);
IloRangeArray FeasAuxConl(env, 0);

//--------Declare Dual Objective function-------------
IloObjective Dual_objective(env, 0);
IloObjective Dual_objective_Aux(env, 0);
IloObjective Dual_objective_FeasAux(env, 0);

//--------Declare Array of Benders Cuts Added in Master Problem-------------
IloRangeArray BendersCuts(env, 0);

//--------Declare DUAL variables (Variables of DSP)----------------
double U1_1Valueijt[imax][jmax][tmax];
double U2_1Valuekjt[kmax][jmax][tmax];
double U3_1Valuezjt[zmax][jmax][tmax];
double U1_2Valueijt[imax][jmax][tmax];
double U2_2Valuekjt[kmax][jmax][tmax];
double U3_2Valuezjt[zmax][jmax][tmax];
double U4Valuezt[zmax][tmax];
double U5Valueizt[imax][zmax][tmax];
double U6Valueizt[imax][zmax][tmax];
double U7Valuekzt[kmax][zmax][tmax];
double U8Valuekzt[kmax][zmax][tmax];
double U9Valuezjt[zmax][jmax][tmax];
double U10Valuezjt[zmax][jmax][tmax];
double U11Valueizt[imax][zmax][tmax];
double U12Valuekzt[kmax][zmax][tmax];
double U13Valueizt[imax][zmax][tmax];
double U14Valuekzt[kmax][zmax][tmax];

IloNumArray U1_1NumValueijt(env, 0);
IloNumArray U2_1NumValuekjt(env, 0);
IloNumArray U3_1NumValuezjt(env, 0);
IloNumArray U1_2NumValueijt(env, 0);
IloNumArray U2_2NumValuekjt(env, 0);
IloNumArray U3_2NumValuezjt(env, 0);
IloNumArray U4NumValuezt(env, 0);
IloNumArray U5NumValueizt(env, 0);
IloNumArray U6NumValueizt(env, 0);
IloNumArray U7NumValuekzt(env, 0);
IloNumArray U8NumValuekzt(env, 0);
IloNumArray U9NumValuezjt(env, 0);
IloNumArray U10NumValuezjt(env, 0);
IloNumArray U11NumValueizt(env, 0);
IloNumArray U12NumValuekzt(env, 0);
IloNumArray U13NumValueizt(env, 0);
IloNumArray U14NumValuekzt(env, 0);

IloNumArray FeasvalsDualRangeSumXijt(env, 0);
IloNumArray SlackValues(env, 0);
IloNum SlackValuesMasterCons;

vector <double> LowerBoundArray;
vector <double> UpperBoundArray;
vector <double> UpperBoundGlobalArray;
vector <double> UpperBoundAuxArray;
vector <double> UpperBoundGlobalAuxArray;
vector <double> dTy;
vector <double> zCurrent;
vector <double> cTx;
vector <double> bTu;
vector <double> cTxAux;
vector <double> bTuAux;
vector <double> BestPrimalSlaveObjSoFar;
vector <double> BestDualSlaveObjSoFar;
vector <double> Time;
vector <double> SlackValuesOfBendersCuts;
vector <double> SlackValuesOfMainMasterCons;
vector <double> NoOfCutsInEachIteration;
vector <double> NoOfCoveredVarsInEachIteration;
vector <bool> SameCutVector;
vector <bool> SameMasterSolutionVector;


typedef struct treenode_tag {
	double  lpbound;  // LP bound
	IloModel  lp;     // ptr to master
	IloModel  lp_cg;   // ptr to colgen
	treenode_tag  *nextnode;  // link to next node in tree
} treenode;

treenode_tag *BBTreeList;

void Found_Error(char *name)
{
	printf("%s failed, exiting...\n", name);
	printf("Press return to continue...\n");
	getchar();
}
int load_data(char* FilePath_Data_ptr) {
	int status;
	char* FileName_ptr;
	char* FileName_ptr2;
	string read_file = "";
	//-------------------Declare Data of the problem--------------------
	for (t = 0; t < tmax; t++) {
		for (i = 0; i < imax; i++) {
			for (j = 0; j < jmax; j++) {
				ae_ijt[i][j][t] = 0;
			}
			E_it[i][t] = 0;
		}
		for (k = 0; k < kmax; k++) {
			for (j = 0; j < jmax; j++) {
				as_kjt[k][j][t] = 0;
			}
			S_kt[k][t] = 0;
		}
	}


	FileName_ptr = FileName_Problem;
	char filepath[1024];
	sprintf(filepath, "%s/%s", FilePath_Data_ptr, FileName_ptr);
	infile.open(filepath);
	if (infile.fail()) {
		printf("%c file could not be opened. Try correcting the file's location path: %c\n", FileName_ptr, FilePath_Data_ptr);
		//cout << " file could not be opened. Try correcting the file's location path." << endl;
		//cout << filepath << endl;
		system("pause");
		exit(1);
	}
	char general[1024];
	cout << "E_it" << endl;;
	for (i = 0; i < imax; i++) {
		for (t = 0; t < tmax; t++) {
			infile >> E_it[i][t];
			cout << E_it[i][t] << '\t';
		}
		cout << endl;
	}
	cout << "ae_ijt" << endl;;
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				infile >> ae_ijt[i][j][t];
				cout << ae_ijt[i][j][t] << '\t';
			}
			cout << endl;
		}
		cout << endl;
	}
	cout << "S_kt" << endl;;
	for (k = 0; k < kmax; k++) {
		for (t = 0; t < tmax; t++) {
			infile >> S_kt[k][t];
			cout << S_kt[k][t] << '\t';
		}
		cout << endl;
	}
	cout << "as_kjt" << endl;;
	for (k = 0; k < kmax; k++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				infile >> as_kjt[k][j][t];
				cout << as_kjt[k][j][t] << '\t';
			}
			cout << endl;
		}
		cout << endl;
	}
	cout << "initial_zj" << endl;
	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			infile >> initial_zj[z][j];
			cout << initial_zj[z][j] << '\t';
		}
		cout << endl;
	}
	infile.close();


	for (z = 0; z < zmax; z++) {
		for (t = 0; t < tmax; t++) {
			for (i = 0; i < imax; i++) {
				CiztValue[i][z][t] = 0;
				SCiztValue[i][z][t] = 0;
				for (j = 0; j < jmax; j++) {
					XizjtValue[i][z][j][t];
					OptimalXizjtValue[i][z][j][t];
				}
			}
			for (k = 0; k < kmax; k++) {
				DkztValue[k][z][t] = 0;
				SDkztValue[k][z][t] = 0;
				for (j = 0; j < jmax; j++) {
					YzkjtValue[z][k][j][t];
					OptimalYzkjtValue[z][k][j][t];
				}
			}
			for (j = 0; j < jmax; j++) {
				FzjtValue[z][j][t] = 0;
				IzjtValue[z][j][t] = 0;
				OptimalFzjtValue[z][j][t] = 0;
				OptimalIzjtValue[z][j][t] = 0;
			}
		}
	}

	// End of DATA///////////////////////////
	return 0;
}
int do_master() {
	char CharMasterVar[60];
	char CharMasterCon[60];
	double LBMasterCon = 0;
	double UBMasterCon = 0;
	NoOfMasterVars = 0;
	NoOfMasterCons = 0;
	//------------------------------------------------------------------------------
	//---------------------------------- MASTER ------------------------------------
	//------------------------------------------------------------------------------
	//----------------------------- Master Variable --------------------------------
	//-------------- Variable de Decision C ---------------------------------------

	for (i = 0; i < imax; i++) {
		IloNumVarMatrix2x2 Czt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray Ct(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharMasterVar, "Cizt(i%d,z%d,t%d)", i, z, t);
				IloNumVar C(env, 0, 1, ILOINT, CharMasterVar);
				NoOfMasterVars++;
				Ct.add(C);
			}
			Czt.add(Ct);
		}
		Cizt.add(Czt);
	}
	//-------------- Variable de Decision D ---------------------------------------

	for (k = 0; k < kmax; k++) {
		IloNumVarMatrix2x2 Dzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray Dt(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharMasterVar, "Dkzt(k%d,z%d,t%d)", k, z, t);
				IloNumVar D(env, 0, 1, ILOINT, CharMasterVar);
				NoOfMasterVars++;
				Dt.add(D);
			}
			Dzt.add(Dt);
		}
		Dkzt.add(Dzt);
	}
	//-------------- Variable de Decision f ---------------------------------------

	for (z = 0; z < zmax; z++) {
		IloNumVarMatrix2x2 Fjt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloNumVarArray Ft(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharMasterVar, "Fzjt(z%d,j%d,t%d)", z, j, t);
				IloNumVar F(env, 0, 1, ILOINT, CharMasterVar);
				NoOfMasterVars++;
				Ft.add(F);
			}
			Fjt.add(Ft);
		}
		Fzjt.add(Fjt);
	}
	//--------------------------- Variable de Decision Z ---------------------------


	for (n = 0; n < 1; n++) {
		sprintf(CharMasterVar, "Zn(n%d)", n);
		IloNumVar Z(env, 0, IloInfinity, ILOFLOAT, CharMasterVar);
		Zn.add(Z);
	}

	//-----------------------------Finish of Master Variables --------------------------------

	//-----------------------------------------------------------------------------
	//-------------------------Start of Master Constraints-----------------------------------------
	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//-------------------------- Contrainte de melange CT3 -------------------------

	for (z = 0; z < zmax; z++) {
		IloRangeArray CT3Melt(env, 0);
		for (t = 0; t < tmax; t++) {
			IloExpr expr(env, 0);
			for (j = 0; j < jmax; j++) {
				expr += Fzjt[z][j][t];
			}
			sprintf(CharMasterCon, "CT3Melzjt(z%d,t%d)", z, t);
			LBMasterCon = 0, UBMasterCon = 1;
			IloRange CT3Mel(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(CT3Mel);
			CT3Melt.add(CT3Mel);
			expr.end();
		}
		CT3Melzt.add(CT3Melt);
	}

	//------------------------------- Chargement CT3 ---------------------------------

	for (i = 0; i < imax; i++) {
		IloRangeMatrix3x3 CT3C_ou_Dkzt(env, 0);
		for (k = 0; k < kmax; k++) {
			IloRangeMatrix2x2 CT3C_ou_Dzt(env, 0);
			for (z = 0; z < zmax; z++) {
				IloRangeArray CT3C_ou_Dt(env, 0);
				for (t = 0; t < tmax; t++) {
					IloExpr expr(env, 0);
					expr += Cizt[i][z][t] + Dkzt[k][z][t];
					sprintf(CharMasterCon, "CT3C_ou_Dzt(z%d,t%d)", z, t);
					LBMasterCon = 0, UBMasterCon = 1;
					IloRange CT3C_ou_D(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
					NoOfMasterCons++;
					modelMaster.add(CT3C_ou_D);
					CT3C_ou_Dt.add(CT3C_ou_D);
					expr.end();
				}
				CT3C_ou_Dzt.add(CT3C_ou_Dt);
			}
			CT3C_ou_Dkzt.add(CT3C_ou_Dzt);
		}
		CT3C_ou_Dikzt.add(CT3C_ou_Dkzt);
	}

	//------------------------------- INITIAL VALUES (t=0) ---------------------------------
	//------------------------------- z tank contains j type at t=0 ---------------------------------

	for (z = 0; z < zmax; z++) {
		IloRangeArray SupFj0(env, 0);
		for (j = 0; j < jmax; j++) {
			IloExpr expr(env, 0);
			expr = Fzjt[z][j][0];
			sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
			LBMasterCon = initial_zj[z][j] / BigM, UBMasterCon = initial_zj[z][j] * BigM;
			IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(SupF0);
			SupFj0.add(SupF0);
			expr.end();
		}
		SupFzj0.add(SupFj0);
	}




	//for (z = 0; z<zmax; z++) {
	//	IloRangeArray SupFj0(env, 0);
	//	for (j = 0; j<jmax; j++) {

	//		if (z == 0) {
	//			if (j == 0) {//------ 0 tank contains 0 type at t=0 ------------
	//				IloExpr expr(env, 0);
	//				expr = Fzjt[z][j][0];
	//				sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
	//				LBMasterCon = 1, UBMasterCon = 1;
	//				IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//				NoOfMasterCons++;
	//				modelMaster.add(SupF0);
	//				SupFj0.add(SupF0);
	//				expr.end();
	//			}
	//			else {
	//				IloExpr expr(env, 0);
	//				expr = Fzjt[z][j][0];
	//				sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
	//				LBMasterCon = 0, UBMasterCon = 0;
	//				IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//				NoOfMasterCons++;
	//				modelMaster.add(SupF0);
	//				SupFj0.add(SupF0);
	//				expr.end();
	//			}
	//		}


	//		if (z == 1) {
	//			if (j == 0) {//------ 1 tank contains 0 type at t=0 ------------
	//				IloExpr expr(env, 0);
	//				expr = Fzjt[z][j][0];
	//				sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
	//				LBMasterCon = 1, UBMasterCon = 1;
	//				IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//				NoOfMasterCons++;
	//				modelMaster.add(SupF0);
	//				SupFj0.add(SupF0);
	//				expr.end();
	//			}
	//			else {
	//				IloExpr expr(env, 0);
	//				expr = Fzjt[z][j][0];
	//				sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
	//				LBMasterCon = 0, UBMasterCon = 0;
	//				IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//				NoOfMasterCons++;
	//				modelMaster.add(SupF0);
	//				SupFj0.add(SupF0);
	//				expr.end();
	//			}
	//		}


	//		if (z == 2) {
	//			if (j == 2) {//------ 2 tank contains 2 type at t=0 ------------
	//				IloExpr expr(env, 0);
	//				expr = Fzjt[z][j][0];
	//				sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
	//				LBMasterCon = 1, UBMasterCon = 1;
	//				IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//				NoOfMasterCons++;
	//				modelMaster.add(SupF0);
	//				SupFj0.add(SupF0);
	//				expr.end();
	//			}
	//			else {
	//				IloExpr expr(env, 0);
	//				expr = Fzjt[z][j][0];
	//				sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
	//				LBMasterCon = 0, UBMasterCon = 0;
	//				IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//				NoOfMasterCons++;
	//				modelMaster.add(SupF0);
	//				SupFj0.add(SupF0);
	//				expr.end();
	//			}
	//		}

	//		if (z == 3) {
	//			if (j == 2) {//------ 3 tank contains 2 type at t=0 ------------
	//				IloExpr expr(env, 0);
	//				expr = Fzjt[z][j][0];
	//				sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
	//				LBMasterCon = 1, UBMasterCon = 1;
	//				IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//				NoOfMasterCons++;
	//				modelMaster.add(SupF0);
	//				SupFj0.add(SupF0);
	//				expr.end();
	//			}

	//			else {
	//				IloExpr expr(env, 0);
	//				expr = Fzjt[z][j][0];
	//				sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
	//				LBMasterCon = 0, UBMasterCon = 0;
	//				IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//				NoOfMasterCons++;
	//				modelMaster.add(SupF0);
	//				SupFj0.add(SupF0);
	//				expr.end();
	//			}

	//		}



	//		if (z == 4) {//------ 4 tank is empty at t=0 ------------
	//			IloExpr expr(env, 0);
	//			expr = Fzjt[z][j][0];
	//			sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
	//			LBMasterCon = 0, UBMasterCon = 0;
	//			IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//			NoOfMasterCons++;
	//			modelMaster.add(SupF0);
	//			SupFj0.add(SupF0);
	//			expr.end();
	//		}

	//		if (z == 5) {//------ 5 tank is empty at t=0 ------------
	//			IloExpr expr(env, 0);
	//			expr = Fzjt[z][j][0];
	//			sprintf(CharMasterCon, "ConSupFzj0(z%d,j%d)", z, j);
	//			LBMasterCon = 0, UBMasterCon = 0;
	//			IloRange SupF0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//			NoOfMasterCons++;
	//			modelMaster.add(SupF0);
	//			SupFj0.add(SupF0);
	//			expr.end();
	//		}

	//	}
	//	SupFzj0.add(SupFj0);
	//}

	//--------------- No loading taking place at t=0 ------------

	for (i = 0; i < imax; i++) {
		IloRangeArray SupCz0(env, 0);
		for (z = 0; z < zmax; z++) {
			IloExpr expr(env, 0);
			expr = Cizt[i][z][0];
			sprintf(CharMasterCon, "ConSupCiz0(i%d,z%d)", i, z);
			LBMasterCon = 0, UBMasterCon = 0;
			IloRange SupC0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(SupC0);
			SupCz0.add(SupC0);
			expr.end();
		}
		SupCiz0.add(SupCz0);
	}

	//--------------- No unloading taking place at t=0 ------------

	for (k = 0; k < kmax; k++) {
		IloRangeArray SupDz0(env, 0);
		for (z = 0; z < zmax; z++) {
			IloExpr expr(env, 0);
			expr = Dkzt[k][z][0];
			sprintf(CharMasterCon, "ConSupDkz0(k%d,z%d)", k, z);
			LBMasterCon = 0, UBMasterCon = 0;
			IloRange SupD0(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(SupD0);
			SupDz0.add(SupD0);
			expr.end();
		}
		SupDkz0.add(SupDz0);
	}

	//-------------------------------Finish of INITIAL VALUES (t=0) ---------------------------------

	//Contrainte de feasabilitι////////////////////////////


	for (i = 0; i < imax; i++) {
		IloRangeArray Con3W1t(env, 0);
		for (t = 0; t < tmax; t++) {
			IloExpr expr(env, 0);
			for (z = 0; z < zmax; z++) {
				expr += Cizt[i][z][t];
			}
			sprintf(CharMasterCon, "CT3W1it(i%d,t%d)", i, t);
			LBMasterCon = E_it[i][t] / 100000, UBMasterCon = IloInfinity;
			IloRange Con3W1(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con3W1);
			Con3W1t.add(Con3W1);
			expr.end();
		}
		Con3W1it.add(Con3W1t);
	}



	for (k = 0; k < kmax; k++) {
		IloRangeArray Con5W2t(env, 0);
		for (t = 0; t < tmax; t++) {
			IloExpr expr(env, 0);
			for (z = 0; z < zmax; z++) {
				expr += Dkzt[k][z][t];
			}
			sprintf(CharMasterCon, "CT5W2kt(k%d,t%d)", k, t);
			LBMasterCon = S_kt[k][t] / 100000, UBMasterCon = IloInfinity;
			IloRange Con5W2(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con5W2);
			Con5W2t.add(Con5W2);
			expr.end();
		}
		Con5W2kt.add(Con5W2t);
	}



	//---------------NO VALID INEQUALITIES-------------------

	//-----------------------------------------------------------------------------
	//-------------------------Finish of Master Constraints-----------------------------------------


	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//---------------------------------Fonction Objectif de master probleme--------------------------
	//------------------------------------------------------------------------------
	IloExpr expr1(env);

	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				expr1 += Cizt[i][z][t];
			}
		}
	}

	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				expr1 += Dkzt[k][z][t];
			}
		}
	}
	for (n = 0; n < 1; n++) {
		expr1 += Zn[n];
	}

	modelMaster.add(IloMinimize(env, expr1));
	expr1.end();

	return 0;
}
int do_dual_slave_and_aux() {
	char CharSlaveVar[60];
	char CharSlaveCon[60];
	double LBSlaveCon = 0;
	double UBSlaveCon = 0;
	NoOfSlaveVars = 0;
	NoOfSlaveCons = 0;

	//--------------------------- PRIMAL SLAVE PROBLEM ----------------------------------
	//------------------------------------------------------------------------------
	//--------------------------- Slave Dual Variables ---------------------------
	//--------------------------- Decision Variable U1_1ijt ---------------------------

	for (i = 0; i < imax; i++) {
		IloNumVarMatrix2x2 U1_1jt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloNumVarArray U1_1t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U1_1ijt(i%d,j%d,t%d)", i, j, t);
				IloNumVar U1_1(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U1_1t.add(U1_1);
				AllVars.add(U1_1);
			}
			U1_1jt.add(U1_1t);
		}
		U1_1ijt.add(U1_1jt);
	}

	//--------------------------- Decision Variable U1_2ijt ---------------------------

	for (i = 0; i < imax; i++) {
		IloNumVarMatrix2x2 U1_2jt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloNumVarArray U1_2t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U1_2ijt(i%d,j%d,t%d)", i, j, t);
				IloNumVar U1_2(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U1_2t.add(U1_2);
				AllVars.add(U1_2);
			}
			U1_2jt.add(U1_2t);
		}
		U1_2ijt.add(U1_2jt);
	}


	//--------------------------- Decision Variable U2_1kjt --------------------------
	for (k = 0; k < kmax; k++) {
		IloNumVarMatrix2x2 U2_1jt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloNumVarArray U2_1t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U2_1kjt(k%d,j%d,t%d)", k, j, t);
				IloNumVar U2_1(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U2_1t.add(U2_1);
				AllVars.add(U2_1);
			}
			U2_1jt.add(U2_1t);
		}
		U2_1kjt.add(U2_1jt);
	}


	//--------------------------- Decision Variable U2_2kjt --------------------------
	for (k = 0; k < kmax; k++) {
		IloNumVarMatrix2x2 U2_2jt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloNumVarArray U2_2t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U2_2kjt(k%d,j%d,t%d)", k, j, t);
				IloNumVar U2_2(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U2_2t.add(U2_2);
				AllVars.add(U2_2);
			}
			U2_2jt.add(U2_2t);
		}
		U2_2kjt.add(U2_2jt);
	}

	//--------------------------- Decision Variable U3_1zjt --------------------------

	for (z = 0; z < zmax; z++) {
		IloNumVarMatrix2x2 U3_1jt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloNumVarArray U3_1t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U3_1zjt(z%d,j%d,t%d)", z, j, t);
				IloNumVar U3_1(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U3_1t.add(U3_1);
				AllVars.add(U3_1);
			}
			U3_1jt.add(U3_1t);
		}
		U3_1zjt.add(U3_1jt);
	}

	//--------------------------- Decision Variable U3_2zjt --------------------------

	for (z = 0; z < zmax; z++) {
		IloNumVarMatrix2x2 U3_2jt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloNumVarArray U3_2t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U3_2zjt(z%d,j%d,t%d)", z, j, t);
				IloNumVar U3_2(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U3_2t.add(U3_2);
				AllVars.add(U3_2);
			}
			U3_2jt.add(U3_2t);
		}
		U3_2zjt.add(U3_2jt);
	}


	//-------------- Decision Variable U4zt ---------------------------------------

	for (z = 0; z < zmax; z++) {
		IloNumVarArray U4t(env, 0);
		for (t = 0; t < tmax; t++) {
			sprintf(CharSlaveVar, "U4zt(z%d,t%d)", z, t);
			IloNumVar U4(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
			NoOfSlaveVars++;
			U4t.add(U4);
			AllVars.add(U4);
		}
		U4zt.add(U4t);
	}


	//-------------- Decision Variable U5izt ---------------------------------------

	for (i = 0; i < imax; i++) {
		IloNumVarMatrix2x2 U5zt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray U5t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U5izt(i%d,z%d,t%d)", i, z, t);
				IloNumVar U5(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U5t.add(U5);
				AllVars.add(U5);
			}
			U5zt.add(U5t);
		}
		U5izt.add(U5zt);
	}

	//-------------- Decision Variable U6izt ---------------------------------------

	for (i = 0; i < imax; i++) {
		IloNumVarMatrix2x2 U6zt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray U6t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U6izt(i%d,z%d,t%d)", i, z, t);
				IloNumVar U6(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U6t.add(U6);
				AllVars.add(U6);
			}
			U6zt.add(U6t);
		}
		U6izt.add(U6zt);
	}

	//-------------- Decision Variable U7kzt ---------------------------------------
	for (k = 0; k < kmax; k++) {
		IloNumVarMatrix2x2 U7zt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray U7t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U7kzt(k%d,z%d,t%d)", k, z, t);
				IloNumVar U7(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U7t.add(U7);
				AllVars.add(U7);
			}
			U7zt.add(U7t);
		}
		U7kzt.add(U7zt);
	}

	//-------------- Decision Variable U8kzt ---------------------------------------

	for (k = 0; k < kmax; k++) {
		IloNumVarMatrix2x2 U8zt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray U8t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U8kzt(k%d,z%d,t%d)", k, z, t);
				IloNumVar U8(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U8t.add(U8);
				AllVars.add(U8);
			}
			U8zt.add(U8t);
		}
		U8kzt.add(U8zt);
	}

	//-------------- Decision Variable U9zjt ---------------------------------------

	for (z = 0; z < zmax; z++) {
		IloNumVarMatrix2x2 U9jt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloNumVarArray U9t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U9zjt(z%d,j%d,t%d)", z, j, t);
				IloNumVar U9(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U9t.add(U9);
				AllVars.add(U9);
			}
			U9jt.add(U9t);
		}
		U9zjt.add(U9jt);
	}

	//-------------- Decision Variable U10zjt ---------------------------------------

	for (z = 0; z < zmax; z++) {
		IloNumVarMatrix2x2 U10jt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloNumVarArray U10t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U10zjt(z%d,j%d,t%d)", z, j, t);
				IloNumVar U10(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U10t.add(U10);
				AllVars.add(U10);
			}
			U10jt.add(U10t);
		}
		U10zjt.add(U10jt);
	}

	//-------------- Decision Variable U11izt ---------------------------------------

	for (i = 0; i < imax; i++) {
		IloNumVarMatrix2x2 U11zt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray U11t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U11izt(i%d,z%d,t%d)", i, z, t);
				IloNumVar U11(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U11t.add(U11);
				AllVars.add(U11);
			}
			U11zt.add(U11t);
		}
		U11izt.add(U11zt);
	}

	//-------------- Decision Variable U12kzt ---------------------------------------

	for (k = 0; k < kmax; k++) {
		IloNumVarMatrix2x2 U12zt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray U12t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U12kzt(k%d,z%d,t%d)", k, z, t);
				IloNumVar U12(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U12t.add(U12);
				AllVars.add(U12);
			}
			U12zt.add(U12t);
		}
		U12kzt.add(U12zt);
	}

	//-------------- Decision Variable U13izt ---------------------------------------

	for (i = 0; i < imax; i++) {
		IloNumVarMatrix2x2 U13zt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray U13t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U13izt(i%d,z%d,t%d)", i, z, t);
				IloNumVar U13(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U13t.add(U13);
				AllVars.add(U13);
			}
			U13zt.add(U13t);
		}
		U13izt.add(U13zt);
	}

	//-------------- Decision Variable U14kzt ---------------------------------------

	for (k = 0; k < kmax; k++) {
		IloNumVarMatrix2x2 U14zt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray U14t(env, 0);
			for (t = 0; t < tmax; t++) {
				sprintf(CharSlaveVar, "U14kzt(k%d,z%d,t%d)", k, z, t);
				IloNumVar U14(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
				NoOfSlaveVars++;
				U14t.add(U14);
				AllVars.add(U14);
			}
			U14zt.add(U14t);
		}
		U14kzt.add(U14zt);
	}


	//----------------- END OF DECISION VARIABLES ------------------
	//-----------------------------------------------------------------------------
	//------------------------- Slave Dual Constraints ------------------------
	//-----------------------------------------------------------------------------
	//------------------------------ Con1Xizjt ------------------------------

	for (i = 0; i < imax; i++) {
		IloRangeMatrix3x3 Con1Xzjt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeMatrix2x2 Con1Xjt(env, 0);
			for (j = 0; j < jmax; j++) {
				IloRangeArray Con1Xt(env, 0);
				for (t = 0; t < tmax; t++) {
					IloExpr expr(env, 0);
					expr += (U1_1ijt[i][j][t] - U1_2ijt[i][j][t]) - (U3_1zjt[z][j][t] - U3_2zjt[z][j][t]) - U5izt[i][z][t] + U6izt[i][z][t];
					sprintf(CharSlaveCon, "Con1Xizjt(i%d,z%d,j%d,t%d)", i, z, j, t);
					LBSlaveCon = -IloInfinity, UBSlaveCon = 0;
					IloRange Con1X(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
					NoOfSlaveCons++;
					modelDualSlave.add(Con1X);
					modelDualSlaveAux.add(Con1X);
					modelDualSlaveFeasAux.add(Con1X);
					Con1Xt.add(Con1X);
					expr.end();
				}
				Con1Xjt.add(Con1Xt);
			}
			Con1Xzjt.add(Con1Xjt);
		}
		Con1Xizjt.add(Con1Xzjt);
	}

	//------------------------------ Con2Yzkjt ------------------------------
	for (z = 0; z < zmax; z++) {
		IloRangeMatrix3x3 Con2Ykjt(env, 0);
		for (k = 0; k < kmax; k++) {
			IloRangeMatrix2x2 Con2Yjt(env, 0);
			for (j = 0; j < jmax; j++) {
				IloRangeArray Con2Yt(env, 0);
				for (t = 0; t < tmax; t++) {
					IloExpr expr(env, 0);
					expr += (U2_1kjt[k][j][t] - U2_2kjt[k][j][t]) + (U3_1zjt[z][j][t] - U3_2zjt[z][j][t]) - U7kzt[k][z][t] + U8kzt[k][z][t];
					sprintf(CharSlaveCon, "Con2Yzkjt(z%d,k%d,j%d,t%d)", z, k, j, t);
					LBSlaveCon = -IloInfinity, UBSlaveCon = 0;
					IloRange Con2Y(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
					NoOfSlaveCons++;
					modelDualSlave.add(Con2Y);
					modelDualSlaveAux.add(Con2Y);
					modelDualSlaveFeasAux.add(Con2Y);
					Con2Yt.add(Con2Y);
					expr.end();
				}
				Con2Yjt.add(Con2Yt);
			}
			Con2Ykjt.add(Con2Yjt);
		}
		Con2Yzkjt.add(Con2Ykjt);
	}


	//------------------------------ Con3Izjt ------------------------------
	for (z = 0; z < zmax; z++) {
		IloRangeMatrix2x2 Con3Ijt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloRangeArray Con3It(env, 0);
			for (t = 0; t < tmax; t++) {
				if (t < tmax - 1) {
					IloExpr expr(env, 0);
					expr += (U3_1zjt[z][j][t] - U3_2zjt[z][j][t]) - (U3_1zjt[z][j][t + 1] - U3_2zjt[z][j][t + 1]) - U4zt[z][t] - U9zjt[z][j][t] + U10zjt[z][j][t];
					sprintf(CharSlaveCon, "Con3Izjt(z%d,j%d,t%d)", z, j, t);
					LBSlaveCon = -IloInfinity, UBSlaveCon = 0;
					IloRange Con3I(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
					NoOfSlaveCons++;
					modelDualSlave.add(Con3I);
					modelDualSlaveAux.add(Con3I);
					modelDualSlaveFeasAux.add(Con3I);
					Con3It.add(Con3I);
					expr.end();
				}
				else {
					IloExpr expr(env, 0);
					expr += (U3_1zjt[z][j][t] - U3_2zjt[z][j][t]) - U4zt[z][t] - U9zjt[z][j][t] + U10zjt[z][j][t];
					sprintf(CharSlaveCon, "Con3Izjt(z%d,j%d,t%d)", z, j, t);
					LBSlaveCon = -IloInfinity, UBSlaveCon = 0;
					IloRange Con3I(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
					NoOfSlaveCons++;
					modelDualSlave.add(Con3I);
					modelDualSlaveAux.add(Con3I);
					modelDualSlaveFeasAux.add(Con3I);
					Con3It.add(Con3I);
					expr.end();
				}
			}
			Con3Ijt.add(Con3It);
		}
		Con3Izjt.add(Con3Ijt);
	}


	//------------------------------ Con4SCizt ------------------------------

	for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 Con4SCzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray Con4SCt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				expr += -U11izt[i][z][t] + U13izt[i][z][t];
				sprintf(CharSlaveCon, "Con4SCizt(i%d,z%d,t%d)", i, z, t);
				LBSlaveCon = -IloInfinity, UBSlaveCon = 1;
				IloRange Con4SC(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
				NoOfSlaveCons++;
				modelDualSlave.add(Con4SC);
				modelDualSlaveAux.add(Con4SC);
				Con4SCt.add(Con4SC);
				expr.end();
			}
			Con4SCzt.add(Con4SCt);
		}
		Con4SCizt.add(Con4SCzt);
	}

	//------------------------------ Con5SDkzt ------------------------------

	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 Con5SDzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray Con5SDt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				expr += -U12kzt[k][z][t] + U14kzt[k][z][t];
				sprintf(CharSlaveCon, "Con5SDzkt(z%d,k%d,t%d)", z, k, t);
				LBSlaveCon = -IloInfinity, UBSlaveCon = 1;
				IloRange Con5SD(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
				NoOfSlaveCons++;
				modelDualSlave.add(Con5SD);
				modelDualSlaveAux.add(Con5SD);
				Con5SDt.add(Con5SD);
				expr.end();
			}
			Con5SDzt.add(Con5SDt);
		}
		Con5SDkzt.add(Con5SDzt);
	}

	//------------------------------ AuxConl ------------------------------
	for (l = 0; l < 1; l++) {
		IloExpr expr(env, 0);
		expr += 0;
		char AuxCon1[60];
		sprintf(AuxCon1, "AuxCon(l%d)", l);
		double LBAuxCon = -1, UBAuxCon = IloInfinity;
		IloRange AuxCon(env, LBAuxCon, expr, UBAuxCon, AuxCon1);
		NoOfSlaveCons++;
		modelDualSlaveAux.add(AuxCon);
		AuxConl.add(AuxCon);
		expr.end();
	}


	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//------------Objective Function of Dual Slave Problem--------------------------
	//------------------------------------------------------------------------------

	/*

	IloExpr expr_slave(env);

	for (i=0;i<imax;i++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	expr_slave+=E[i][t]*aeijt[i][j][t]*U1ijt[i][j][t];
	}
	}
	}
	for (k=0;k<kmax;k++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	expr_slave+=S[k][t]*askjt[k][j][t]*U2kjt[k][j][t];
	}
	}
	}
	for (z=0;z<zmax;z++){
	for (j=0;j<jmax;j++){
	//for (t=0;t<tmax;t++){
	expr_slave+=initial[z][j]*U3zjt[z][j][0];
	//}
	}
	}

	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	expr_slave+=-Cap*U4zt[z][t];
	}
	}
	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	expr_slave+=-BigM*CiztValue[i][z][t]*U5izt[i][z][t];
	}
	}
	}
	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	expr_slave+=CiztValue[i][z][t]*U6izt[i][z][t];
	}
	}
	}
	for (z=0;z<zmax;z++){
	for (k=0;k<kmax;k++){
	for (t=0;t<tmax;t++){
	expr_slave+=-BigM*DzktValue[z][k][t]*U7kzt[z][k][t];
	}
	}
	}
	for (z=0;z<zmax;z++){
	for (k=0;k<kmax;k++){
	for (t=0;t<tmax;t++){
	expr_slave+=DzktValue[z][k][t]*U8kzt[z][k][t];
	}
	}
	}
	for (z=0;z<zmax;z++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	expr_slave+=-BigM*FzjtValue[z][j][t]*U9zjt[z][j][t];
	}
	}
	}
	for (z=0;z<zmax;z++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	expr_slave+=FzjtValue[z][j][t]*U10zjt[z][j][t];
	}
	}
	}
	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	expr_slave+=-CiztValue[i][z][t]*U11izt[i][z][t];
	}
	}
	}
	for (z=0;z<zmax;z++){
	for (k=0;k<kmax;k++){
	for (t=0;t<tmax;t++){
	expr_slave+=-DzktValue[z][k][t]*U12kzt[z][k][t];
	}
	}
	}
	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	if(t==0){
	expr_slave+=CiztValue[i][z][t]*U13izt[i][z][t];
	}else{
	expr_slave+=(CiztValue[i][z][t]-CiztValue[i][z][t-1])*U13izt[i][z][t];
	}
	}
	}
	}
	for (z=0;z<zmax;z++){
	for (k=0;k<kmax;k++){
	for (t=0;t<tmax;t++){
	if(t==0){
	expr_slave+=DzktValue[z][k][t]*U14kzt[z][k][t];
	}else{
	expr_slave+=(DzktValue[z][k][t]-DzktValue[z][k][t-1])*U14kzt[z][k][t];
	}
	}
	}
	}


	modelDualSlave.add(IloMaximize(env, expr_slave));
	expr_slave.end();
	*/

	Dual_objective = IloAdd(modelDualSlave, IloMaximize(env, 0));
	Dual_objective_Aux = IloAdd(modelDualSlaveAux, IloMaximize(env, 0));

	return 0;
}
int do_dual_FeasAux() {
	char CharSlaveCon[60];
	double LBSlaveCon = 0;
	double UBSlaveCon = 0;


	//ADD ONLY THE CONSTRAINTS OF FEASIBLE AUXILIARY DSP THAT ARE DIFFERENT FROM THE OTHER PROBLEMS
	//-----------------------------------------------------------------------------
	//------------------------- Slave Dual Constraints ------------------------
	//-----------------------------------------------------------------------------

	//------------------------------ Con4AuxSCizt ------------------------------
	//ADD THIS CONSTRAINT IN AUXILIARY DSP (FEAS) INSTEAD OF Con4SCizt

	for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 Con4AuxSCzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray Con4AuxSCt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				expr += -U11izt[i][z][t] + U13izt[i][z][t];
				sprintf(CharSlaveCon, "Con4AuxSCizt(i%d,z%d,t%d)", i, z, t);
				LBSlaveCon = -IloInfinity, UBSlaveCon = 0;//In the Classical DSP UBSlaveCon =1
				IloRange ConAux4SC(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
				//NoOfSlaveCons++;
				modelDualSlaveFeasAux.add(ConAux4SC);
				Con4AuxSCt.add(ConAux4SC);
				expr.end();
			}
			Con4AuxSCzt.add(Con4AuxSCt);
		}
		Con4AuxSCizt.add(Con4AuxSCzt);
	}


	//------------------------------ Con5AuxSDkzt ------------------------------
	//ADD THIS CONSTRAINT IN AUXILIARY DSP (FEAS) INSTEAD OF Con5SDkzt
	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 Con5AuxSDzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray Con5AuxSDt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				expr += -U12kzt[k][z][t] + U14kzt[k][z][t];
				sprintf(CharSlaveCon, "Con5SDzkt(z%d,k%d,t%d)", z, k, t);
				LBSlaveCon = -IloInfinity, UBSlaveCon = 0;//In the Classical DSP UBSlaveCon =1
				IloRange Con5AuxSD(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
				//NoOfSlaveCons++;
				modelDualSlaveFeasAux.add(Con5AuxSD);
				Con5AuxSDt.add(Con5AuxSD);
				expr.end();
			}
			Con5AuxSDzt.add(Con5AuxSDt);
		}
		Con5AuxSDkzt.add(Con5AuxSDzt);
	}



	//------------------------------ ExtraAuxConstraint ------------------------------
	//In the Classical DSP there is no ExtraAuxConstraint
	for (l = 0; l < 1; l++) {
		IloExpr expr(env, 0);
		for (t = 0; t < tmax; t++) {
			for (j = 0; j < jmax; j++) {
				for (i = 0; i < imax; i++) {
					expr += U1_1ijt[i][j][t];
					expr += U1_2ijt[i][j][t];
				}
				for (k = 0; k < kmax; k++) {
					expr += U2_1kjt[k][j][t];
					expr += U2_2kjt[k][j][t];
				}
			}
			for (z = 0; z < zmax; z++) {
				expr += U4zt[z][t];
				for (i = 0; i < imax; i++) {
					expr += U5izt[i][z][t];
					expr += U6izt[i][z][t];
					expr += U11izt[i][z][t];
					expr += U13izt[i][z][t];
				}
				for (k = 0; k < kmax; k++) {
					expr += U7kzt[k][z][t];
					expr += U8kzt[k][z][t];
					expr += U12kzt[k][z][t];
					expr += U14kzt[k][z][t];
				}
				for (j = 0; j < jmax; j++) {
					expr += U3_1zjt[z][j][t];
					expr += U3_2zjt[z][j][t];
					expr += U9zjt[z][j][t];
					expr += U10zjt[z][j][t];
				}

			}
		}
		sprintf(CharSlaveCon, "ExtraAuxConstraintl(l%d)", l);
		LBSlaveCon = 1, UBSlaveCon = 1;
		IloRange ExtraAuxCon(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
		NoOfSlaveCons++;
		modelDualSlaveFeasAux.add(ExtraAuxCon);
		ExtraAuxConl.add(ExtraAuxCon);
		expr.end();
	}

	//------------------------------ FeasAuxConl ------------------------------
	for (l = 0; l < 1; l++) {
		IloExpr expr(env, 0);
		expr += 0;
		char FeasAuxCon1[60];
		sprintf(FeasAuxCon1, "FeasAuxCon(l%d)", l);
		double LBFeasAuxCon = -IloInfinity, UBFeasAuxCon = 1;
		IloRange FeasAuxCon(env, LBFeasAuxCon, expr, UBFeasAuxCon, FeasAuxCon1);
		NoOfSlaveCons++;
		modelDualSlaveFeasAux.add(FeasAuxCon);
		FeasAuxConl.add(FeasAuxCon);
		expr.end();
	}



	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//------------Objective Function of Dual Slave Problem--------------------------
	//------------------------------------------------------------------------------

	Dual_objective_FeasAux = IloAdd(modelDualSlaveFeasAux, IloMaximize(env, 0));

	return 0;
}

int Solve_Master(IloModel modelMaster_ptr, IloCplex cplexMaster_ptr, double *DTransposeY_ptr, bool *InfeasibleMaster = false, bool *SameMasterSolution = false) {

	cplexMaster_ptr.extract(modelMaster_ptr);
	//--------------SOLVE MASTER PROBLEM----------------	
	try {
		cplexMaster_ptr.exportModel("CurrentMaster.lp");
		cplexMaster_ptr.setOut(env.getNullStream());
		cplexMaster_ptr.solve();

		if (!cplexMaster_ptr.solve()) {
			env.error() << "Failed to optimize Master Problem" << endl;
			env.out() << "----------------------------------------------------------------" << endl;
			*InfeasibleMaster = true;
			return 0;
		}

		//env.out() << "Solution status Master = " << cplexMaster_ptr.getStatus() << endl;
		//env.out() << "Solution value Master= " << cplexMaster_ptr.getObjValue() << endl;

		//--------LOWER BOUND------------
		LowerBound = cplexMaster_ptr.getObjValue();

		*SameMasterSolution = true;
		for (t = 0; t < tmax; t++) {
			for (z = 0; z < zmax; z++) {
				for (i = 0; i < imax; i++) {
					if (CiztValue[i][z][t] != cplexMaster_ptr.getValue(Cizt[i][z][t])) {
						*SameMasterSolution = false;
					}
				}
				for (k = 0; k < kmax; k++) {
					if (DkztValue[k][z][t] != cplexMaster_ptr.getValue(Dkzt[k][z][t])) {
						*SameMasterSolution = false;
					}
				}
				for (j = 0; j < jmax; j++) {
					if (FzjtValue[z][j][t] != cplexMaster_ptr.getValue(Fzjt[z][j][t])) {
						*SameMasterSolution = false;
					}
				}
			}
		}
		for (n = 0; n < 1; n++) {
			if (ThetaValue != cplexMaster_ptr.getValue(Zn[n])) {
				*SameMasterSolution = false;
			}
		}

		for (t = 0; t < tmax; t++) {
			for (z = 0; z < zmax; z++) {
				for (i = 0; i < imax; i++) {
					CiztValue[i][z][t] = cplexMaster_ptr.getValue(Cizt[i][z][t]);
				}
				for (k = 0; k < kmax; k++) {
					DkztValue[k][z][t] = cplexMaster_ptr.getValue(Dkzt[k][z][t]);
				}
				for (j = 0; j < jmax; j++) {
					FzjtValue[z][j][t] = cplexMaster_ptr.getValue(Fzjt[z][j][t]);
				}
			}
		}

		for (n = 0; n < 1; n++) {
			ThetaValue = cplexMaster_ptr.getValue(Zn[n]);
		}

		for (t = 0; t < tmax; t++) {
			for (z = 0; z < zmax; z++) {
				for (i = 0; i < imax; i++) {
					*DTransposeY_ptr += CiztValue[i][z][t];
				}
				for (k = 0; k < kmax; k++) {
					*DTransposeY_ptr += DkztValue[k][z][t];
				}
			}
		}
		dTy.push_back(*DTransposeY_ptr);
		zCurrent.push_back(ThetaValue);

		OptimalThetaValue = ThetaValue;





	}
	catch (IloException& e) {
		cerr << "concert exception caught Master:" << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught Master " << endl;
	}
	return 0;
}
int Get_Slack_Values(IloCplex cplexMaster_ptr) {
	//---------------Get SLACK values of the constraints of MASTER problem----------------

	for (z = 0; z < zmax; z++) {
		for (t = 0; t < tmax; t++) {
			SlackValuesMasterCons = cplexMaster_ptr.getSlack(CT3Melzt[z][t]);
			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
		}
	}
	for (i = 0; i < imax; i++) {
		for (k = 0; k < kmax; k++) {
			for (z = 0; z < zmax; z++) {
				for (t = 0; t < tmax; t++) {
					SlackValuesMasterCons = cplexMaster_ptr.getSlack(CT3C_ou_Dikzt[i][k][z][t]);
					SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
				}
			}
		}
	}

	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			SlackValuesMasterCons = cplexMaster_ptr.getSlack(SupFzj0[z][j]);
			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
		}
	}
	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			SlackValuesMasterCons = cplexMaster_ptr.getSlack(SupCiz0[i][z]);
			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
		}
	}
	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			SlackValuesMasterCons = cplexMaster_ptr.getSlack(SupDkz0[k][z]);
			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
		}
	}
	for (i = 0; i < imax; i++) {
		for (t = 0; t < tmax; t++) {
			SlackValuesMasterCons = cplexMaster_ptr.getSlack(Con3W1it[i][t]);
			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
		}
	}
	for (k = 0; k < kmax; k++) {
		for (t = 0; t < tmax; t++) {
			SlackValuesMasterCons = cplexMaster_ptr.getSlack(Con5W2kt[k][t]);
			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
		}
	}
	/*
	IloRangeMatrix2x2 CT3Melzt(env,0);
	IloRangeMatrix2x2 CT3C_ou_Dzt(env,0);
	IloRangeMatrix2x2 SupFzj0(env,0);
	IloRangeMatrix2x2 SupCiz0(env,0);
	IloRangeMatrix2x2 SupDkz0(env,0);
	IloRangeMatrix2x2 Con3W1it(env,0);
	IloRangeMatrix2x2 Con5W2kt(env,0);
	*/
	//	cout<<"size of SLACK Array ="<<SlackValues.getSize()<<endl;

	cplexMaster_ptr.getSlacks(SlackValues, BendersCuts);
	//	cout<<"size of SLACK Array ="<<SlackValues.getSize()<<endl;

	for (l = 0; l < SlackValues.getSize(); l++) {
		/*
		if(SlackValues[l]!=0){
		cout<<"SlackValues["<<l<<"]="<<SlackValues[l]<<endl;
		}
		*/
		SlackValuesOfBendersCuts.push_back(SlackValues[l]);
	}
	/*

	for (l=0;l<SlackValuesOfBendersCuts.size();l++){

	cout<<"SlackValuesOfBendersCuts["<<l<<"]="<<SlackValuesOfBendersCuts[l]<<endl;

	}
	*/
	return 0;
}
int UpdateDualSlaveObjective(IloObjective Dual_objective_ptr) {
	int l = 0;
	//---------------Update the objective function of the DUAL SLAVE problem---------------- 
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			IloNumArray Dual_Obj_Coefs_U1_1(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U1_1[l] = E_it[i][t] * ae_ijt[i][j][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U1_1ijt[i][j], Dual_Obj_Coefs_U1_1);
		}
	}
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			IloNumArray Dual_Obj_Coefs_U1_2(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U1_2[l] = -E_it[i][t] * ae_ijt[i][j][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U1_2ijt[i][j], Dual_Obj_Coefs_U1_2);
		}
	}
	for (k = 0; k < kmax; k++) {
		for (j = 0; j < jmax; j++) {
			IloNumArray Dual_Obj_Coefs_U2_1(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U2_1[l] = S_kt[k][t] * as_kjt[k][j][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U2_1kjt[k][j], Dual_Obj_Coefs_U2_1);
		}
	}
	for (k = 0; k < kmax; k++) {
		for (j = 0; j < jmax; j++) {
			IloNumArray Dual_Obj_Coefs_U2_2(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U2_2[l] = -S_kt[k][t] * as_kjt[k][j][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U2_2kjt[k][j], Dual_Obj_Coefs_U2_2);
		}
	}
	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			IloNum Dual_Obj_Coefs_U3_1;
			for (t = 0; t < 1; t++) {
				Dual_Obj_Coefs_U3_1 = initial_zj[z][j];
			}
			Dual_objective_ptr.setLinearCoef(U3_1zjt[z][j][0], Dual_Obj_Coefs_U3_1);//setLinearCoefs(U3zjt[z][j],Dual_Obj_Coefs_U3);
		}
	}
	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			IloNum Dual_Obj_Coefs_U3_2;
			for (t = 0; t < 1; t++) {
				Dual_Obj_Coefs_U3_2 = -initial_zj[z][j];
			}
			Dual_objective_ptr.setLinearCoef(U3_2zjt[z][j][0], Dual_Obj_Coefs_U3_2);//setLinearCoefs(U3zjt[z][j],Dual_Obj_Coefs_U3);
		}
	}
	for (z = 0; z < zmax; z++) {
		IloNumArray Dual_Obj_Coefs_U4(env, tmax);
		l = 0;
		for (t = 0; t < tmax; t++) {
			Dual_Obj_Coefs_U4[l] = -capmax;
			l++;
		}
		Dual_objective_ptr.setLinearCoefs(U4zt[z], Dual_Obj_Coefs_U4);
	}
	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			IloNumArray Dual_Obj_Coefs_U5(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U5[l] = -BigM * CiztValue[i][z][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U5izt[i][z], Dual_Obj_Coefs_U5);
		}
	}

	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			IloNumArray Dual_Obj_Coefs_U6(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U6[l] = CiztValue[i][z][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U6izt[i][z], Dual_Obj_Coefs_U6);
		}
	}

	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			IloNumArray Dual_Obj_Coefs_U7(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U7[l] = -BigM * DkztValue[k][z][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U7kzt[k][z], Dual_Obj_Coefs_U7);
		}
	}

	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			IloNumArray Dual_Obj_Coefs_U8(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U8[l] = DkztValue[k][z][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U8kzt[k][z], Dual_Obj_Coefs_U8);
		}
	}

	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			IloNumArray Dual_Obj_Coefs_U9(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U9[l] = -BigM * FzjtValue[z][j][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U9zjt[z][j], Dual_Obj_Coefs_U9);
		}
	}

	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			IloNumArray Dual_Obj_Coefs_U10(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U10[l] = FzjtValue[z][j][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U10zjt[z][j], Dual_Obj_Coefs_U10);
		}
	}
	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			IloNumArray Dual_Obj_Coefs_U11(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U11[l] = -CiztValue[i][z][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U11izt[i][z], Dual_Obj_Coefs_U11);
		}
	}

	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			IloNumArray Dual_Obj_Coefs_U12(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				Dual_Obj_Coefs_U12[l] = -DkztValue[k][z][t];
				l++;
			}
			Dual_objective_ptr.setLinearCoefs(U12kzt[k][z], Dual_Obj_Coefs_U12);
		}
	}
	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			IloNumArray Dual_Obj_Coefs_U13(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				if (t == 0) {
					Dual_Obj_Coefs_U13[l] = CiztValue[i][z][t];
					l++;
				}
				else {
					Dual_Obj_Coefs_U13[l] = (CiztValue[i][z][t] - CiztValue[i][z][t - 1]);
					l++;
				}
			}
			Dual_objective_ptr.setLinearCoefs(U13izt[i][z], Dual_Obj_Coefs_U13);
		}
	}


	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			IloNumArray Dual_Obj_Coefs_U14(env, tmax);
			l = 0;
			for (t = 0; t < tmax; t++) {
				if (t == 0) {
					Dual_Obj_Coefs_U14[l] = DkztValue[k][z][t];
					l++;
				}
				else {
					Dual_Obj_Coefs_U14[l] = (DkztValue[k][z][t] - DkztValue[k][z][t - 1]);
					l++;
				}
			}
			Dual_objective_ptr.setLinearCoefs(U14kzt[k][z], Dual_Obj_Coefs_U14);
		}
	}


	return 0;
}
int UpdateDualSlaveAuxCon() {

	AuxConl[0].setExpr(Dual_objective.getExpr());
	AuxConl[0].setLB(LowestDualSlaveObjFunction);

	return 0;
}
int UpdateDualSlaveFeasAuxCon() {

	FeasAuxConl[0].setExpr(Dual_objective_FeasAux.getExpr());
	FeasAuxConl[0].setUB(LowestFeasAuxDualSlaveObjFunction);

	return 0;
}
/*int UpdateSlaveRHS(){
//---------------Update the LB of the constraints of SLAVE problem----------------

for (z=0;z<zmax;z++){
for (t=0;t<tmax;t++){
for(i=0;i<imax;i++){
CT1Fonctionement_Cizt[i][z][t].setLB(-m*CiztValue[i][z][t]);
CT2Fonctionement_Cizt[i][z][t].setLB(CiztValue[i][z][t]);
SC2_Cizt[i][z][t].setLB(-1*CiztValue[i][z][t]);
}
for(k=0;k<kmax;k++){
CT1Fonctionement_Dkzt[k][z][t].setLB(-m*DkztValue[k][z][t]);
CT2Fonctionement_Dkzt[k][z][t].setLB(DkztValue[k][z][t]);
SD2_Dkzt[k][z][t].setLB(-1*DkztValue[k][z][t]);
}
for (j=0;j<jmax;j++){
CT1Melzjt[z][j][t].setLB(-m*FzjtValue[z][j][t]);
CT2Melzjt[z][j][t].setLB(FzjtValue[z][j][t]);
}
}
}

for(i=0;i<imax;i++){
for (z=0;z<zmax;z++){
for (t=0;t<tmax;t++){
if(t==0){
SC_Cizt[i][z][t].setLB(CiztValue[i][z][t]);
}else{
SC_Cizt[i][z][t].setLB(CiztValue[i][z][t]-CiztValue[i][z][t-1]);
}
}
}
}
for(k=0;k<kmax;k++){
for (z=0;z<zmax;z++){
for (t=0;t<tmax;t++){
if(t==0){
SD_Dkzt[k][z][t].setLB(DkztValue[k][z][t]);
}else{
SD_Dkzt[k][z][t].setLB(DkztValue[k][z][t]-DkztValue[k][z][t-1]);
}
}
}
}
return 0;
}*/
int Solve_Dual_Slave(IloModel modelDualSlave_ptr, IloCplex cplexDualSlave_ptr) {

	cplexDualSlave_ptr.extract(modelDualSlave_ptr);
	//-----------Solve Slave Problem--------------
	try {

		cplexDualSlave_ptr.setParam(IloCplex::PreInd, 0);
		cplexDualSlave_ptr.setParam(IloCplex::ScaInd, -1);
		cplexDualSlave_ptr.setParam(IloCplex::RootAlg, IloCplex::Primal);
		cplexDualSlave_ptr.exportModel("CurrentDualSlave.lp");
		cplexDualSlave_ptr.setOut(env.getNullStream());
		cplexDualSlave_ptr.solve();
		//env.out() << "Solution status of DUAL SLAVE problem = " << cplexDualSlave_ptr.getStatus() << endl;
		//env.out() << "Solution value of DUAL SLAVE problem = " << cplexDualSlave_ptr.getObjValue() << endl;

		for (t = 0; t < tmax; t++) {
			for (j = 0; j < jmax; j++) {
				for (i = 0; i < imax; i++) {
					U1_1Valueijt[i][j][t] = cplexDualSlave_ptr.getValue(U1_1ijt[i][j][t]);
					U1_2Valueijt[i][j][t] = cplexDualSlave_ptr.getValue(U1_2ijt[i][j][t]);
				}
				for (k = 0; k < kmax; k++) {
					U2_1Valuekjt[k][j][t] = cplexDualSlave_ptr.getValue(U2_1kjt[k][j][t]);
					U2_2Valuekjt[k][j][t] = cplexDualSlave_ptr.getValue(U2_2kjt[k][j][t]);
				}
				for (z = 0; z < zmax; z++) {
					U3_1Valuezjt[z][j][t] = cplexDualSlave_ptr.getValue(U3_1zjt[z][j][t]);
					U3_2Valuezjt[z][j][t] = cplexDualSlave_ptr.getValue(U3_2zjt[z][j][t]);
					U9Valuezjt[z][j][t] = cplexDualSlave_ptr.getValue(U9zjt[z][j][t]);
					U10Valuezjt[z][j][t] = cplexDualSlave_ptr.getValue(U10zjt[z][j][t]);
				}
			}
			for (z = 0; z < zmax; z++) {
				U4Valuezt[z][t] = cplexDualSlave_ptr.getValue(U4zt[z][t]);
				for (i = 0; i < imax; i++) {
					U5Valueizt[i][z][t] = cplexDualSlave_ptr.getValue(U5izt[i][z][t]);
					U6Valueizt[i][z][t] = cplexDualSlave_ptr.getValue(U6izt[i][z][t]);
					U11Valueizt[i][z][t] = cplexDualSlave_ptr.getValue(U11izt[i][z][t]);
					U13Valueizt[i][z][t] = cplexDualSlave_ptr.getValue(U13izt[i][z][t]);
				}
				for (k = 0; k < kmax; k++) {
					U7Valuekzt[k][z][t] = cplexDualSlave_ptr.getValue(U7kzt[k][z][t]);
					U8Valuekzt[k][z][t] = cplexDualSlave_ptr.getValue(U8kzt[k][z][t]);
					U12Valuekzt[k][z][t] = cplexDualSlave_ptr.getValue(U12kzt[k][z][t]);
					U14Valuekzt[k][z][t] = cplexDualSlave_ptr.getValue(U14kzt[k][z][t]);
				}
			}
		}


	}//end of try(try of primal slave 1)

	catch (IloException& e) {
		cerr << "concert exception caught:" << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught" << endl;
	}
	return 0;
}
int Dual_Slave_Unbounded(double *DualSlaveObjFunction, double *PrimalSlaveObjFunction) {
	//env.error() << "Dual Slave Problem is UNBOUNDED" << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	//------Upper Bound Global remains the same--------
	UpperBound = 100;
	UpperBoundGlobal = UpperBoundGlobal;

	*PrimalSlaveObjFunction = 0;
	*DualSlaveObjFunction = BigM;
	return 0;
}
int Aux_Dual_Slave_Unbounded(double *AuxDualSlaveObjFunction, double *AuxPrimalSlaveObjFunction) {
	//env.error() << "Auxiliary Dual Slave Problem is UNBOUNDED" << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	//------Upper Bound Global remains the same--------
	UpperBoundAux = 100;
	UpperBoundGlobalAux = UpperBoundGlobalAux;

	*AuxPrimalSlaveObjFunction = 0;
	*AuxDualSlaveObjFunction = BigM;
	return 0;
}
int Dual_Slave_Bounded(IloCplex cplexDualSlave_ptr, double *DTransposeY, double *DualSlaveObjFunction, double *PrimalSlaveObjFunction, int *FirstTime_ptr, int loop_ptr, int *NoOfTimes_ptr, IloModel modelDualSlaveAux_ptr_ptr, int *NoofTimesWorseSolutionFound) {
	//env.error() << "Dual Slave Problem is BOUNDED" << endl;
	//env.error() << "Found a FEASIBLE solution of Slave LP" << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	*DualSlaveObjFunction = cplexDualSlave_ptr.getObjValue();
	int status = 0;
	for (t = 0; t < tmax; t++) {
		for (z = 0; z < zmax; z++) {
			for (i = 0; i < imax; i++) {
				SCiztValue[i][z][t] = cplexDualSlave_ptr.getDual(Con4SCizt[i][z][t]);
			}
			for (k = 0; k < kmax; k++) {
				SDkztValue[k][z][t] = cplexDualSlave_ptr.getDual(Con5SDkzt[k][z][t]);
			}
			for (j = 0; j < jmax; j++) {
				for (i = 0; i < imax; i++) {
					XizjtValue[i][z][j][t] = cplexDualSlave_ptr.getDual(Con1Xizjt[i][z][j][t]);
				}
				for (k = 0; k < kmax; k++) {
					YzkjtValue[z][k][j][t] = cplexDualSlave_ptr.getDual(Con2Yzkjt[z][k][j][t]);
				}
				IzjtValue[z][j][t] = cplexDualSlave_ptr.getDual(Con3Izjt[z][j][t]);
			}
		}
	}
	*PrimalSlaveObjFunction = 0;
	for (t = 0; t < tmax; t++) {
		for (z = 0; z < zmax; z++) {
			for (i = 0; i < imax; i++) {
				*PrimalSlaveObjFunction += SCiztValue[i][z][t];
			}
			for (k = 0; k < kmax; k++) {
				*PrimalSlaveObjFunction += SDkztValue[k][z][t];
			}
		}
	}

	UpperBound = *DTransposeY + *PrimalSlaveObjFunction;
	if (UpperBound > UpperBoundGlobal) {//-----We found a worse feasible solution---
		*NoofTimesWorseSolutionFound = *NoofTimesWorseSolutionFound + 1;
	}

	if (UpperBound >= UpperBoundGlobal) {//-----We found a no better feasible solution---
		UpperBoundGlobal = UpperBoundGlobal;
	}
	else {//-----------We found a better feasible solution-------
		UpperBoundGlobal = UpperBound;//Update Upper Bound
		OptimalOriginalObjFunction = UpperBoundGlobal;
		OptimalMasterObjFunction = *DTransposeY;
		OptimalPrimalSlaveObjFunction = *PrimalSlaveObjFunction;
		OptimalDualSlaveObjFunction = *DualSlaveObjFunction;
		LowestDualSlaveObjFunction = OptimalDualSlaveObjFunction;

		//-----------Update the Auxiliary Cut-------------
		status = UpdateDualSlaveAuxCon();
		if (status != 0) {
			Found_Error("UpdateDualSlaveAuxCon");
			return -1;
		}
		//----------------------------------------------
		for (t = 0; t < tmax; t++) {
			for (z = 0; z < zmax; z++) {
				for (i = 0; i < imax; i++) {
					OptimalCiztValue[i][z][t] = CiztValue[i][z][t];
					OptimalSCiztValue[i][z][t] = SCiztValue[i][z][t];
				}
				for (k = 0; k < kmax; k++) {
					OptimalDkztValue[k][z][t] = DkztValue[k][z][t];
					OptimalSDkztValue[k][z][t] = SDkztValue[k][z][t];
				}
				for (j = 0; j < jmax; j++) {
					OptimalFzjtValue[z][j][t] = FzjtValue[z][j][t];
				}
				for (j = 0; j < jmax; j++) {
					for (i = 0; i < imax; i++) {
						OptimalXizjtValue[i][z][j][t] = XizjtValue[i][z][j][t];
					}
					for (k = 0; k < kmax; k++) {
						OptimalYzkjtValue[z][k][j][t] = YzkjtValue[z][k][j][t];
					}
					OptimalIzjtValue[z][j][t] = IzjtValue[z][j][t];
				}
			}
		}

		OptimalThetaValue = ThetaValue;

	}//end of else (better feasible solution found)



	return 0;
}
int Aux_Dual_Slave_Bounded(IloCplex cplexDualSlave_ptr, double *DTransposeY, double *AuxDualSlaveObjFunction, double *AuxPrimalSlaveObjFunction, int *FirstTime_ptr, int loop_ptr, int *NoOfTimes_ptr, IloModel modelDualSlaveAux_ptr_ptr, int *NoofTimesWorseSolutionFound) {
	//env.error() << "Auxiliary Dual Slave Problem is BOUNDED" << endl;
	//env.error() << "Found a FEASIBLE solution of Slave LP" << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	*AuxDualSlaveObjFunction = cplexDualSlave_ptr.getObjValue();
	int status = 0;
	for (t = 0; t < tmax; t++) {
		for (z = 0; z < zmax; z++) {
			for (i = 0; i < imax; i++) {
				SCiztValue[i][z][t] = cplexDualSlave_ptr.getDual(Con4SCizt[i][z][t]);
			}
			for (k = 0; k < kmax; k++) {
				SDkztValue[k][z][t] = cplexDualSlave_ptr.getDual(Con5SDkzt[k][z][t]);
			}
			for (j = 0; j < jmax; j++) {
				for (i = 0; i < imax; i++) {
					XizjtValue[i][z][j][t] = cplexDualSlave_ptr.getDual(Con1Xizjt[i][z][j][t]);
				}
				for (k = 0; k < kmax; k++) {
					YzkjtValue[z][k][j][t] = cplexDualSlave_ptr.getDual(Con2Yzkjt[z][k][j][t]);
				}
				IzjtValue[z][j][t] = cplexDualSlave_ptr.getDual(Con3Izjt[z][j][t]);
			}
		}
	}
	*AuxPrimalSlaveObjFunction = 0;
	for (t = 0; t < tmax; t++) {
		for (z = 0; z < zmax; z++) {
			for (i = 0; i < imax; i++) {
				*AuxPrimalSlaveObjFunction += SCiztValue[i][z][t];
			}
			for (k = 0; k < kmax; k++) {
				*AuxPrimalSlaveObjFunction += SDkztValue[k][z][t];
			}
		}
	}

	UpperBoundAux = *DTransposeY + *AuxPrimalSlaveObjFunction;


	if (UpperBoundAux > UpperBoundGlobalAux) {//-----We found a worse feasible solution---
		UpperBoundGlobalAux = UpperBoundGlobalAux;
	}
	else {//-----------We found a better feasible solution-------
		UpperBoundGlobalAux = UpperBoundAux;//Update Upper Bound
		OptimalOriginalObjFunction = UpperBoundGlobalAux;
		OptimalMasterObjFunction = *DTransposeY;
		OptimalPrimalSlaveObjFunction = *AuxPrimalSlaveObjFunction;
		OptimalDualSlaveObjFunction = *AuxDualSlaveObjFunction;
		LowestDualSlaveObjFunction = OptimalDualSlaveObjFunction;

		//-----------Update the Auxiliary Cut-------------
		status = UpdateDualSlaveAuxCon();
		if (status != 0) {
			Found_Error("UpdateDualSlaveAuxCon");
			return -1;
		}
		//----------------------------------------------
		for (t = 0; t < tmax; t++) {
			for (z = 0; z < zmax; z++) {
				for (i = 0; i < imax; i++) {
					OptimalCiztValue[i][z][t] = CiztValue[i][z][t];
					OptimalSCiztValue[i][z][t] = SCiztValue[i][z][t];
				}
				for (k = 0; k < kmax; k++) {
					OptimalDkztValue[k][z][t] = DkztValue[k][z][t];
					OptimalSDkztValue[k][z][t] = SDkztValue[k][z][t];
				}
				for (j = 0; j < jmax; j++) {
					OptimalFzjtValue[z][j][t] = FzjtValue[z][j][t];
				}
				for (j = 0; j < jmax; j++) {
					for (i = 0; i < imax; i++) {
						OptimalXizjtValue[i][z][j][t] = XizjtValue[i][z][j][t];
					}
					for (k = 0; k < kmax; k++) {
						OptimalYzkjtValue[z][k][j][t] = YzkjtValue[z][k][j][t];
					}
					OptimalIzjtValue[z][j][t] = IzjtValue[z][j][t];
				}
			}
		}

		OptimalThetaValue = ThetaValue;
	}//end of else (better feasible solution found)



	return 0;
}

int GetExtremeRayOfDSP(IloCplex cplexDualSlave_ptr) {
	//----------------Get an extreme ray of the DUAL SLAVE problem-------------
	//cout<<"size of Array ="<<FeasvalsDualRangeSumXijt.getSize()<<endl;

	//cplexSlave_ptr.dualFarkas(SumXijt[0][0],FeasvalsDualRangeSumXijt);
	//cout<<"size of Array ="<<FeasvalsDualRangeSumXijt.getSize()<<endl;
	/*
	for (l=0;l<FeasvalsDualRangeSumXijt.getSize();l++){
	if(FeasvalsDualRangeSumXijt[l]!=0){
	cout<<"FeasvalsDualRangeSumXijt["<<l<<"]="<<FeasvalsDualRangeSumXijt[l]<<endl;
	}
	}
	*/


	//IloExpr ray=cplexDualSlave_ptr.getRay();
	//System.out.println("getRay returned " + ray.toString());


	for (t = 0; t < tmax; t++) {
		for (j = 0; j < jmax; j++) {
			for (i = 0; i < imax; i++) {
				U1_1Valueijt[i][j][t] = 0;
				U1_2Valueijt[i][j][t] = 0;
			}
			for (k = 0; k < kmax; k++) {
				U2_1Valuekjt[k][j][t] = 0;
				U2_2Valuekjt[k][j][t] = 0;
			}
			for (z = 0; z < zmax; z++) {
				U3_1Valuezjt[z][j][t] = 0;
				U3_2Valuezjt[z][j][t] = 0;
				U9Valuezjt[z][j][t] = 0;
				U10Valuezjt[z][j][t] = 0;
			}
		}
		for (z = 0; z < zmax; z++) {
			U4Valuezt[z][t] = 0;
			for (i = 0; i < imax; i++) {
				U5Valueizt[i][z][t] = 0;
				U6Valueizt[i][z][t] = 0;
				U11Valueizt[i][z][t] = 0;
				U13Valueizt[i][z][t] = 0;
			}
			for (k = 0; k < kmax; k++) {
				U7Valuekzt[k][z][t] = 0;
				U8Valuekzt[k][z][t] = 0;
				U12Valuekzt[k][z][t] = 0;
				U14Valuekzt[k][z][t] = 0;
			}
		}
	}


	//cout<<"size of variables ="<<AllVars.getSize()<<endl;
	//cout<<"size of Array ="<<U1NumValueijt.getSize()<<endl;
	cplexDualSlave_ptr.getRay(U1_1NumValueijt, AllVars);

	//cout<<"size of Array ="<<U1NumValueijt.getSize()<<endl;
	//cout<<"size of variables ="<<AllVars.getSize()<<endl;

	//IloNumExpr rayantonis;
	//cplexDualSlave_ptr.getRay(rayantonis,U1ijt[0][0]);
	//for (l = 0; l<U1_1NumValueijt.getSize(); l++) {
	//	if (U1_1NumValueijt[l] != 0) {
	//		//cout<<"U1NumValueijt["<<l<<"]="<<U1NumValueijt[l]<<endl;
	//	}
	//}

	//sprintf(Dual1,"U1ijt(i%d,j%d,t%d)",i,j,t);
	//for ( l = 0; l < U1NumValueijt.getSize(); ++l){
	//cout << l << ", " << U1NumValueijt[l] << " [" << U1ijt[l].getImpl() << "]"<<endl;

	//}

	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U1_1ijt[i][j][t].getId()) {
						U1_1Valueijt[i][j][t] = U1_1NumValueijt[l];
						//cout<<"U1Valueijt["<<i<<"]["<<j<<"]["<<t<<"] ="<<U1Valueijt[i][j][t]<<endl;
					}
					else {
						//U1Valueijt[i][j][t]=0;
					}
				}
			}
		}
	}
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U1_2ijt[i][j][t].getId()) {
						U1_2Valueijt[i][j][t] = U1_1NumValueijt[l];
						//cout<<"U1Valueijt["<<i<<"]["<<j<<"]["<<t<<"] ="<<U1Valueijt[i][j][t]<<endl;
					}
					else {
						//U1Valueijt[i][j][t]=0;
					}
				}
			}
		}
	}
	for (k = 0; k < kmax; k++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U2_1kjt[k][j][t].getId()) {
						U2_1Valuekjt[k][j][t] = U1_1NumValueijt[l];
						//cout<<"U2Valuekjt["<<k<<"]["<<j<<"]["<<t<<"] ="<<U2Valuekjt[k][j][t]<<endl;
					}
					else {
						//U2Valuekjt[k][j][t]=0;
					}
				}
			}
		}
	}
	for (k = 0; k < kmax; k++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U2_2kjt[k][j][t].getId()) {
						U2_2Valuekjt[k][j][t] = U1_1NumValueijt[l];
						//cout<<"U2Valuekjt["<<k<<"]["<<j<<"]["<<t<<"] ="<<U2Valuekjt[k][j][t]<<endl;
					}
					else {
						//U2Valuekjt[k][j][t]=0;
					}
				}
			}
		}
	}
	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U3_1zjt[z][j][t].getId()) {
						U3_1Valuezjt[z][j][t] = U1_1NumValueijt[l];
						//cout<<"U3Valuezjt["<<z<<"]["<<j<<"]["<<t<<"] ="<<U3Valuezjt[z][j][t]<<endl;
					}
					else {
						//U3Valuezjt[z][j][t]=0;
					}
				}
			}
		}
	}
	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U3_2zjt[z][j][t].getId()) {
						U3_2Valuezjt[z][j][t] = U1_1NumValueijt[l];
						//cout<<"U3Valuezjt["<<z<<"]["<<j<<"]["<<t<<"] ="<<U3Valuezjt[z][j][t]<<endl;
					}
					else {
						//U3Valuezjt[z][j][t]=0;
					}
				}
			}
		}
	}
	for (z = 0; z < zmax; z++) {
		for (t = 0; t < tmax; t++) {
			for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
				if (AllVars[l].getId() == U4zt[z][t].getId()) {
					U4Valuezt[z][t] = U1_1NumValueijt[l];
					//cout<<"U4Valuezt["<<z<<"]["<<t<<"] ="<<U4Valuezt[z][t]<<endl;
				}
				else {
					//U4Valuezt[z][t]=0;
				}
			}
		}
	}

	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U5izt[i][z][t].getId()) {
						U5Valueizt[i][z][t] = U1_1NumValueijt[l];
						//cout<<"U5Valueizt["<<i<<"]["<<z<<"]["<<t<<"] ="<<U5Valueizt[i][z][t]<<endl;
					}
					else {
						//U5Valueizt[i][z][t]=0;
					}
				}
			}
		}
	}
	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U6izt[i][z][t].getId()) {
						U6Valueizt[i][z][t] = U1_1NumValueijt[l];
						//cout<<"U6Valueizt["<<i<<"]["<<z<<"]["<<t<<"] ="<<U6Valueizt[i][z][t]<<endl;
					}
					else {
						//U6Valueizt[i][z][t]=0;
					}
				}
			}
		}
	}
	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U7kzt[k][z][t].getId()) {
						U7Valuekzt[k][z][t] = U1_1NumValueijt[l];
						//cout<<"U7Valuekzt["<<k<<"]["<<z<<"]["<<t<<"] ="<<U7Valuekzt[k][z][t]<<endl;
					}
					else {
						//U7Valuekzt[k][z][t]=0;
					}
				}
			}
		}
	}
	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U8kzt[k][z][t].getId()) {
						U8Valuekzt[k][z][t] = U1_1NumValueijt[l];
						//cout<<"U8Valuekzt["<<k<<"]["<<z<<"]["<<t<<"] ="<<U8Valuekzt[k][z][t]<<endl;
					}
					else {
						//U8Valuekzt[k][z][t]=0;
					}
				}
			}
		}
	}

	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U9zjt[z][j][t].getId()) {
						U9Valuezjt[z][j][t] = U1_1NumValueijt[l];
						//cout<<"U9Valuezjt["<<z<<"]["<<j<<"]["<<t<<"] ="<<U9Valuezjt[z][j][t]<<endl;
					}
					else {
						//U9Valuezjt[z][j][t]=0;
					}
				}
			}
		}
	}
	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U10zjt[z][j][t].getId()) {
						U10Valuezjt[z][j][t] = U1_1NumValueijt[l];
						//cout<<"U10Valuezjt["<<z<<"]["<<j<<"]["<<t<<"] ="<<U10Valuezjt[z][j][t]<<endl;
					}
					else {
						//U10Valuezjt[z][j][t]=0;
					}
				}
			}
		}
	}
	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U11izt[i][z][t].getId()) {
						U11Valueizt[i][z][t] = U1_1NumValueijt[l];
						//cout<<"U11Valueizt["<<i<<"]["<<z<<"]["<<t<<"] ="<<U11Valueizt[i][z][t]<<endl;
					}
					else {
						//U11Valueizt[i][z][t]=0;
					}
				}
			}
		}
	}
	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U12kzt[k][z][t].getId()) {
						U12Valuekzt[k][z][t] = U1_1NumValueijt[l];
						//cout<<"U12Valuekzt["<<k<<"]["<<z<<"]["<<t<<"] ="<<U12Valuekzt[k][z][t]<<endl;
					}
					else {
						//U12Valuekzt[k][z][t]=0;
					}
				}
			}
		}
	}
	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U13izt[i][z][t].getId()) {
						U13Valueizt[i][z][t] = U1_1NumValueijt[l];
						//cout<<"U13Valueizt["<<i<<"]["<<z<<"]["<<t<<"] ="<<U13Valueizt[i][z][t]<<endl;
					}
					else {
						//U13Valueizt[i][z][t]=0;
					}
				}
			}
		}
	}

	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				for (l = 0; l < U1_1NumValueijt.getSize(); l++) {
					if (AllVars[l].getId() == U14kzt[k][z][t].getId()) {
						U14Valuekzt[k][z][t] = U1_1NumValueijt[l];
						//cout<<"U14Valuekzt["<<k<<"]["<<z<<"]["<<t<<"] ="<<U14Valuekzt[k][z][t]<<endl;
					}
					else {
						//U14Valuekzt[k][z][t]=0;
					}
				}
			}
		}
	}


	/*
	for (i=0;i<imax;i++){
	for (j=0;j<jmax;j++){
	cout<<"size of Array ="<<U1NumValueijt.getSize()<<endl;
	cplexDualSlave_ptr.getRay(U1NumValueijt,U1ijt[i][j]);
	cout<<"size of Array ="<<U1NumValueijt.getSize()<<endl;
	l=0;
	for (t=0;t<tmax;t++){
	U1Valueijt[i][j][t]=U1NumValueijt[l];
	l++;
	}
	}
	}


	for (k=0;k<kmax;k++){
	for (j=0;j<jmax;j++){
	cout<<"size of Array ="<<U2NumValuekjt.getSize()<<endl;
	cplexDualSlave_ptr.getRay(U2NumValuekjt,U2kjt[k][j]);
	cout<<"size of Array ="<<U2NumValuekjt.getSize()<<endl;
	l=0;
	for (t=0;t<tmax;t++){
	U2Valuekjt[k][j][t]=U2NumValuekjt[l];
	l++;
	}
	}
	}
	for(z=0;z<zmax;z++){
	for (j=0;j<jmax;j++){
	cout<<"size of Array ="<<U3NumValuezjt.getSize()<<endl;
	cplexDualSlave_ptr.getRay(U3NumValuezjt,U3zjt[z][j]);
	cout<<"size of Array ="<<U3NumValuezjt.getSize()<<endl;
	l=0;
	for (t=0;t<tmax;t++){
	U3Valuezjt[z][j][t]=U3NumValuezjt[l];
	l++;
	}
	}
	}
	for(z=0;z<zmax;z++){
	for (j=0;j<jmax;j++){
	cplexDualSlave_ptr.getRay(U9NumValuezjt,U9zjt[z][j]);
	l=0;
	for (t=0;t<tmax;t++){
	U9Valuezjt[z][j][t]=U9NumValuezjt[l];
	l++;
	}
	}
	}
	for(z=0;z<zmax;z++){
	for (j=0;j<jmax;j++){
	cplexDualSlave_ptr.getRay(U10NumValuezjt,U10zjt[z][j]);
	l=0;
	for (t=0;t<tmax;t++){
	U10Valuezjt[z][j][t]=U10NumValuezjt[l];
	l++;
	}
	}
	}

	for(z=0;z<zmax;z++){
	cplexDualSlave_ptr.getRay(U4NumValuezt,U4zt[z]);
	l=0;
	for (t=0;t<tmax;t++){
	U4Valuezt[z][t]=U4NumValuezt[l];
	l++;
	}
	}
	for (i=0;i<imax;i++){
	for(z=0;z<zmax;z++){
	cplexDualSlave_ptr.getRay(U5NumValueizt,U5izt[i][z]);
	l=0;
	for (t=0;t<tmax;t++){
	U5Valueizt[i][z][t]=U5NumValueizt[l];
	l++;
	}
	}
	}
	for (i=0;i<imax;i++){
	for(z=0;z<zmax;z++){
	cplexDualSlave_ptr.getRay(U6NumValueizt,U6izt[i][z]);
	l=0;
	for (t=0;t<tmax;t++){
	U6Valueizt[i][z][t]=U6NumValueizt[l];
	l++;
	}
	}
	}
	for (i=0;i<imax;i++){
	for(z=0;z<zmax;z++){
	cplexDualSlave_ptr.getRay(U11NumValueizt,U11izt[i][z]);
	l=0;
	for (t=0;t<tmax;t++){
	U11Valueizt[i][z][t]=U11NumValueizt[l];
	l++;
	}
	}
	}

	for (i=0;i<imax;i++){
	for(z=0;z<zmax;z++){
	cplexDualSlave_ptr.getRay(U13NumValueizt,U13izt[i][z]);
	l=0;
	for (t=0;t<tmax;t++){
	U13Valueizt[i][z][t]=U13NumValueizt[l];
	l++;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for(z=0;z<zmax;z++){
	cplexDualSlave_ptr.getRay(U7NumValuekzt,U7kzt[k][z]);
	l=0;
	for (t=0;t<tmax;t++){
	U7Valuekzt[k][z][t]=U7NumValuekzt[l];
	l++;
	}
	}
	}
	for (k=0;k<kmax;k++){
	for(z=0;z<zmax;z++){
	cplexDualSlave_ptr.getRay(U8NumValuekzt,U8kzt[k][z]);
	l=0;
	for (t=0;t<tmax;t++){
	U8Valuekzt[k][z][t]=U8NumValuekzt[l];
	l++;
	}
	}
	}
	for (k=0;k<kmax;k++){
	for(z=0;z<zmax;z++){
	cplexDualSlave_ptr.getRay(U12NumValuekzt,U12kzt[k][z]);
	l=0;
	for (t=0;t<tmax;t++){
	U12Valuekzt[k][z][t]=U12NumValuekzt[l];
	l++;
	}
	}
	}
	for (k=0;k<kmax;k++){
	for(z=0;z<zmax;z++){
	cplexDualSlave_ptr.getRay(U14NumValuekzt,U14kzt[k][z]);
	l=0;
	for (t=0;t<tmax;t++){
	U14Valuekzt[k][z][t]=U14NumValuekzt[l];
	l++;
	}
	}
	}
	*/



	/*
	l=0;
	for (i=0;i<imax;i++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	S2valsDualSumXijt[i][j][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}
	for (i=0;i<imax;i++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	S22valsDualSumXijt[i][j][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	S2valsDualSumYkjt[k][j][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}
	for (k=0;k<kmax;k++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	S22valsDualSumYkjt[k][j][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (z=0;z<zmax;z++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	S2valsDualCTIzjt[z][j][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (z=0;z<zmax;z++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	S22valsDualCTIzjt[z][j][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	S2valsDualSum_Izt[z][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}

	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	S2valsDualCT1Fonctionement_Cizt[i][z][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	S2valsDualCT2Fonctionement_Cizt[i][z][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	S2valsDualCT1Fonctionement_Dkzt[k][z][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	S2valsDualCT2Fonctionement_Dkzt[k][z][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}


	for (z=0;z<zmax;z++){
	for(j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	S2valsDualCT1Melzjt[z][j][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (z=0;z<zmax;z++){
	for(j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	S2valsDualCT2Melzjt[z][j][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	S2valsDualSC2_Cizt[i][z][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	S2valsDualSD2_Dkzt[k][z][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	S2valsDualSC_Cizt[i][z][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	S2valsDualSD_Dkzt[k][z][t]=FeasvalsDualRangeSumXijt[l];
	l++;
	}
	}
	}
	*/

	return 0;
}
int GetExtremePointOfDSP(IloCplex cplexDualSlave_ptr) {
	//---------------------Get an extreme point of DUAL SLAVE problem--------------------
	/*
	for (i=0;i<imax;i++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	valsDualRangeSumXijt=cplexSlave_ptr.getDual(SumXijt[i][j][t]);
	S2valsDualSumXijt[i][j][t]=valsDualRangeSumXijt;

	valsDualRangeSumXijt=cplexSlave_ptr.getDual(DSumXijt[i][j][t]);
	S22valsDualSumXijt[i][j][t]=valsDualRangeSumXijt;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	valsDualRangeSumYkjt=cplexSlave_ptr.getDual(SumYkjt[k][j][t]);
	S2valsDualSumYkjt[k][j][t]=valsDualRangeSumYkjt;

	valsDualRangeSumYkjt=cplexSlave_ptr.getDual(DSumYkjt[k][j][t]);
	S22valsDualSumYkjt[k][j][t]=valsDualRangeSumYkjt;
	}
	}
	}

	for (z=0;z<zmax;z++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	valsDualRangeCTIzjt=cplexSlave_ptr.getDual(CTIzjt[z][j][t]);
	S2valsDualCTIzjt[z][j][t]=valsDualRangeCTIzjt;

	valsDualRangeCTIzjt=cplexSlave_ptr.getDual(DCTIzjt[z][j][t]);
	S22valsDualCTIzjt[z][j][t]=valsDualRangeCTIzjt;
	}
	}
	}

	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	valsDualRangeSum_Izt=cplexSlave_ptr.getDual(Sum_Izt[z][t]);
	S2valsDualSum_Izt[z][t]=valsDualRangeSum_Izt;

	}
	}


	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	valsDualRangeCT1Fonctionement_Cizt=cplexSlave_ptr.getDual(CT1Fonctionement_Cizt[i][z][t]);
	S2valsDualCT1Fonctionement_Cizt[i][z][t]=valsDualRangeCT1Fonctionement_Cizt;
	}
	}
	}

	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	valsDualRangeCT2Fonctionement_Cizt=cplexSlave_ptr.getDual(CT2Fonctionement_Cizt[i][z][t]);
	S2valsDualCT2Fonctionement_Cizt[i][z][t]=valsDualRangeCT2Fonctionement_Cizt;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	valsDualRangeCT1Fonctionement_Dkzt=cplexSlave_ptr.getDual(CT1Fonctionement_Dkzt[k][z][t]);
	S2valsDualCT1Fonctionement_Dkzt[k][z][t]=valsDualRangeCT1Fonctionement_Dkzt;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	valsDualRangeCT2Fonctionement_Dkzt=cplexSlave_ptr.getDual(CT2Fonctionement_Dkzt[k][z][t]);
	S2valsDualCT2Fonctionement_Dkzt[k][z][t]=valsDualRangeCT2Fonctionement_Dkzt;
	}
	}
	}


	for (z=0;z<zmax;z++){
	for(j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	valsDualRangeCT1Melzjt=cplexSlave_ptr.getDual(CT1Melzjt[z][j][t]);
	S2valsDualCT1Melzjt[z][j][t]=valsDualRangeCT1Melzjt;
	}
	}
	}

	for (z=0;z<zmax;z++){
	for(j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	valsDualRangeCT2Melzjt=cplexSlave_ptr.getDual(CT2Melzjt[z][j][t]);
	S2valsDualCT2Melzjt[z][j][t]=valsDualRangeCT2Melzjt;
	}
	}
	}

	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	valsDualRangeSC2_Cizt=cplexSlave_ptr.getDual(SC2_Cizt[i][z][t]);
	S2valsDualSC2_Cizt[i][z][t]=valsDualRangeSC2_Cizt;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	valsDualRangeSD2_Dkzt=cplexSlave_ptr.getDual(SD2_Dkzt[k][z][t]);
	S2valsDualSD2_Dkzt[k][z][t]=valsDualRangeSD2_Dkzt;
	}
	}
	}

	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	valsDualRangeSC_Cizt=cplexSlave_ptr.getDual(SC_Cizt[i][z][t]);
	S2valsDualSC_Cizt[i][z][t]=valsDualRangeSC_Cizt;
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	valsDualRangeSD_Dkzt=cplexSlave_ptr.getDual(SD_Dkzt[k][z][t]);
	S2valsDualSD_Dkzt[k][z][t]=valsDualRangeSD_Dkzt;
	}
	}
	}
	*/
	return 0;
}
int CreateBendersCut(int FeasOrOpt, IloExpr expr101) {
	//---------CREATION OF BENDERS CUT--------------- 
	//If FeasOrOpt=0, then a FEASIBILITY CUT is created
	//If FeasOrOpt=1, then a OPTIMALITY CUT is created

	for (t = 0; t < tmax; t++) {
		for (j = 0; j < jmax; j++) {
			for (i = 0; i < imax; i++) {
				expr101 += U1_1Valueijt[i][j][t] * (E_it[i][t] * ae_ijt[i][j][t]);
				expr101 += U1_2Valueijt[i][j][t] * (-E_it[i][t] * ae_ijt[i][j][t]);
				//expr101+=S22valsDualSumXijt[i][j][t]*(-E[i][t]*ae[i][j][t]);
			}
			for (k = 0; k < kmax; k++) {
				expr101 += U2_1Valuekjt[k][j][t] * (S_kt[k][t] * as_kjt[k][j][t]);
				expr101 += U2_2Valuekjt[k][j][t] * (-S_kt[k][t] * as_kjt[k][j][t]);
				//expr101+=S22valsDualSumYkjt[k][j][t]*(-S[k][t]*as[k][j][t]);
			}
		}
		for (z = 0; z < zmax; z++) {
			expr101 += U4Valuezt[z][t] * (-1 * capmax);
			for (i = 0; i < imax; i++) {
				expr101 += U5Valueizt[i][z][t] * (-BigM * Cizt[i][z][t]);
				expr101 += U6Valueizt[i][z][t] * (Cizt[i][z][t]);
				expr101 += U11Valueizt[i][z][t] * (-1 * Cizt[i][z][t]);
				if (t == 0) {
					expr101 += U13Valueizt[i][z][t] * (Cizt[i][z][t]);
				}
				else {
					expr101 += U13Valueizt[i][z][t] * (Cizt[i][z][t] - Cizt[i][z][t - 1]);
				}
			}
			for (j = 0; j < jmax; j++) {
				expr101 += U9Valuezjt[z][j][t] * (-BigM * Fzjt[z][j][t]);
				expr101 += U10Valuezjt[z][j][t] * (Fzjt[z][j][t]);
			}
			for (k = 0; k < kmax; k++) {
				expr101 += U7Valuekzt[k][z][t] * (-BigM * Dkzt[k][z][t]);
				expr101 += U8Valuekzt[k][z][t] * (Dkzt[k][z][t]);
				expr101 += U12Valuekzt[k][z][t] * (-1 * Dkzt[k][z][t]);
				if (t == 0) {
					expr101 += U14Valuekzt[k][z][t] * (Dkzt[k][z][t]);
				}
				else {
					expr101 += U14Valuekzt[k][z][t] * (Dkzt[k][z][t] - Dkzt[k][z][t - 1]);
				}
			}
		}
	}

	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			expr101 += U3_1Valuezjt[z][j][0] * (initial_zj[z][j]);
			expr101 += U3_2Valuezjt[z][j][0] * (-initial_zj[z][j]);
			//expr101+=S22valsDualCTIzjt[z][j][0]*(-initial[z][j]);
		}
	}
	/*
	for (i=0;i<imax;i++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	expr101+=S2valsDualSumXijt[i][j][t]*(E[i][t]*ae[i][j][t]);
	expr101+=S22valsDualSumXijt[i][j][t]*(-E[i][t]*ae[i][j][t]);
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	expr101+=S2valsDualSumYkjt[k][j][t]*(S[k][t]*as[k][j][t]);
	expr101+=S22valsDualSumYkjt[k][j][t]*(-S[k][t]*as[k][j][t]);
	}
	}
	}

	for (z=0;z<zmax;z++){
	for (j=0;j<jmax;j++){
	expr101+=S2valsDualCTIzjt[z][j][0]*(initial[z][j]);
	expr101+=S22valsDualCTIzjt[z][j][0]*(-initial[z][j]);
	}
	}

	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	expr101+=S2valsDualSum_Izt[z][t]*(-1*capmax);
	}
	}

	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	expr101+=S2valsDualCT1Fonctionement_Cizt[i][z][t]*(-m*Cizt[i][z][t]);
	expr101+=S2valsDualCT2Fonctionement_Cizt[i][z][t]*(Cizt[i][z][t]);
	expr101+=S2valsDualSC2_Cizt[i][z][t]*(-1*Cizt[i][z][t]);
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	expr101+=S2valsDualCT1Fonctionement_Dkzt[k][z][t]*(-m*Dkzt[k][z][t]);
	expr101+=S2valsDualCT2Fonctionement_Dkzt[k][z][t]*(Dkzt[k][z][t]);
	expr101+=S2valsDualSD2_Dkzt[k][z][t]*(-1*Dkzt[k][z][t]);
	}
	}
	}

	for (z=0;z<zmax;z++){
	for(j=0;j<jmax;j++){
	for (t=0;t<tmax;t++){
	expr101+=S2valsDualCT1Melzjt[z][j][t]*(-m*Fzjt[z][j][t]);
	expr101+=S2valsDualCT2Melzjt[z][j][t]*(Fzjt[z][j][t]);
	}
	}
	}


	for (i=0;i<imax;i++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	if(t==0){
	expr101+=S2valsDualSC_Cizt[i][z][t]*(Cizt[i][z][t]);
	}else{
	expr101+=S2valsDualSC_Cizt[i][z][t]*(Cizt[i][z][t]-Cizt[i][z][t-1]);
	}
	}
	}
	}

	for (k=0;k<kmax;k++){
	for (z=0;z<zmax;z++){
	for (t=0;t<tmax;t++){
	if(t==0){
	expr101+=S2valsDualSD_Dkzt[k][z][t]*(Dkzt[k][z][t]);
	}else{
	expr101+=S2valsDualSD_Dkzt[k][z][t]*(Dkzt[k][z][t]-Dkzt[k][z][t-1]);
	}
	}
	}
	}
	*/

	if (FeasOrOpt == 1) {//then create an Optimality cut
		for (n = 0; n < 1; n++) {
			expr101 -= Zn[n];
		}
	}

	return 0;
}
int AddBendersCutToMaster(int FeasOrOpt, IloExpr expr101, int loop, IloModel modelMaster_ptr, bool FromAux_ptr, bool FromFeasAux_ptr) {
	//--------------ADD BENDERS  CUT TO MASTER----------------
	//If FeasOrOpt=0, then a FEASIBILITY CUT is added
	//If FeasOrOpt=1, then a OPTIMALITY CUT is added
	char MasterCut[90];

	if (FeasOrOpt == 0) {
		if (FromAux_ptr == true) {
			sprintf(MasterCut, "FeasibilityCutFromAuxiliaryDSP(iter%d)", loop);
			BDFeasCutsFromAux++;
		}
		else if (FromFeasAux_ptr == true) {
			sprintf(MasterCut, "FeasibilityCutFromFeasAuxDSP(iter%d)", loop);
			BDFeasCutsFromFeasAux++;
		}
		else {
			sprintf(MasterCut, "FeasibilityCutFromClassicalDSP(iter%d)", loop);
			BDFeasCutsFromClass++;
		}
		BDFeasCuts++;
	}
	else if (FeasOrOpt == 1) {
		if (FromAux_ptr == true) {
			sprintf(MasterCut, "OptimalityCutFromAuxiliaryDSP(iter%d)", loop);
			BDOptCutsFromAux++;
		}
		else if (FromFeasAux_ptr == true) {
			sprintf(MasterCut, "OptimalityCutFromFeasAuxDSP(iter%d)", loop);
			BDOptCutsFromFeasAux++;
		}
		else {
			sprintf(MasterCut, "OptimalityCutFromClassicalDSP(iter%d)", loop);
			BDOptCutsFromClass++;
		}
		BDOptCuts++;
	}

	double LB101 = -IloInfinity, UB101 = 0;
	IloRange CTMaster(env, LB101, expr101, UB101, MasterCut);
	BendersCuts.add(CTMaster);
	modelMaster_ptr.add(CTMaster);
	CutsPerIteration++;

	return 0;
}
int BendersIteration(IloModel modelMaster_ptr, IloModel modelDualSlave_ptr, IloModel modelDualSlaveAux_ptr, IloModel modelDualSlaveFeasAux_ptr, int *loop_iter, int *NoofTimesWorseSolutionFound) {

	bool InfeasibleMaster = false;
	bool SameCut = false;
	bool SameMasterSolution = false;
	bool NeedClassicalDSP = false;
	bool FoundFeasibleSolution = false;
	bool FromAux = false;
	bool FromFeasAux = false;
	int loop = 0, FirstTime = 10000000000, NoOfTimes = -1, FirstTimeFeas = 10000000000;
	int ClassicalDualStatus;
	int DualStatus;
	int status;
	int CoveredVariables;

	IloCplex cplexDualSlave_ptr(env);
	IloCplex cplexDualSlaveAux_ptr(env);
	IloCplex cplexDualSlaveFeasAux_ptr(env);
	IloCplex cplexMaster_ptr(env);

	cplexDualSlave_ptr.extract(modelDualSlave_ptr);
	cplexDualSlave_ptr.exportModel("modelDualSlave.lp");

	cplexDualSlaveAux_ptr.extract(modelDualSlaveAux_ptr);
	cplexDualSlaveAux_ptr.exportModel("modelDualSlaveAux.lp");

	cplexDualSlaveFeasAux_ptr.extract(modelDualSlaveFeasAux_ptr);
	cplexDualSlaveFeasAux_ptr.exportModel("modelDualSlaveFeasAux.lp");

	cplexMaster_ptr.extract(modelMaster_ptr);
	cplexMaster_ptr.exportModel("modelMaster.lp");

	double DTransposeY = 0, DualSlaveObjFunction = BigM, PrimalSlaveObjFunction = 0;
	double AuxDualSlaveObjFunction = BigM, AuxPrimalSlaveObjFunction = 0;
	double FeasAuxDualSlaveObjFunction = BigM, FeasAuxPrimalSlaveObjFunction = 0;
	double BestSlaveObj = BigM;

	LowerBoundArray.clear();
	UpperBoundArray.clear();
	UpperBoundGlobalArray.clear();
	UpperBoundAuxArray.clear();
	UpperBoundGlobalAuxArray.clear();
	dTy.clear();
	zCurrent.clear();
	cTx.clear();
	bTu.clear();
	cTxAux.clear();
	bTuAux.clear();
	BestPrimalSlaveObjSoFar.clear();
	BestDualSlaveObjSoFar.clear();
	Time.clear();
	SlackValuesOfBendersCuts.clear();
	SlackValuesOfMainMasterCons.clear();
	NoOfCutsInEachIteration.clear();
	SameCutVector.clear();
	SameMasterSolutionVector.clear();

	BDFeasCuts = 0;
	BDOptCuts = 0;
	BDFeasCutsFromAux = 0;
	BDOptCutsFromAux = 0;
	BDFeasCutsFromFeasAux = 0;
	BDOptCutsFromFeasAux = 0;
	BDFeasCutsFromClass = 0;
	BDOptCutsFromClass = 0;

	while (UpperBoundGlobal - LowerBound > epsilon && loop < 5000 && duration < maxhours * 3600) {
		loop++;
		cout << "-----------------" << endl;
		cout << "Iteration =" << loop << endl;
		cout << "-----------------" << endl;
		CutsPerIteration = 0;
		CoveredVariables = 0;
		DTransposeY = 0;

		status = Solve_Master(modelMaster_ptr, cplexMaster_ptr, &DTransposeY, &InfeasibleMaster, &SameMasterSolution);
		if (status != 0) {
			Found_Error("Solve_Master");
			return -1;
		}

		if (InfeasibleMaster == true) {
			break;
		}

		status = Get_Slack_Values(cplexMaster_ptr);
		if (status != 0) {
			Found_Error("Get_Slack_Values");
			return -1;
		}
		if (SameMasterSolution == true) {
			NeedClassicalDSP = true;
			NoOfSameMasterSolution++;
		}


		//----ALWAYS SOLVE CLASSICAL DSP------
		status = UpdateDualSlaveObjective(Dual_objective);
		if (status != 0) {
			Found_Error("UpdateDualSlaveObjective");
			return -1;
		}
		/*status = UpdateDualSlaveObjective(Dual_objective_Aux);
		if (status != 0) {
		Found_Error("UpdateDualSlaveObjective");
		return -1;
		}*/

		status = Solve_Dual_Slave(modelDualSlave_ptr, cplexDualSlave_ptr);
		if (status != 0) {
			Found_Error("Solve_Dual_Slave");
			return -1;
		}

		ClassicalDualStatus = cplexDualSlave_ptr.getStatus();

		if (ClassicalDualStatus == 4) { //---------IF CLASSICAL DUAL SLAVE IS UNBOUNDED-----

			status = Dual_Slave_Unbounded(&DualSlaveObjFunction, &PrimalSlaveObjFunction);
			if (status != 0) {
				Found_Error("Dual_Slave_Unbounded");
				return -1;
			}



			//if (FoundFeasibleSolution == false && SameMasterSolution == false && NeedClassicalDSP == false) {//if we haven't found a feasible solution yet
			//	status = UpdateDualSlaveObjective(Dual_objective_FeasAux);
			//	if (status != 0) {
			//		Found_Error("UpdateDualSlaveObjective");
			//		return -1;
			//	}
			//	status = Solve_Dual_Slave(modelDualSlaveFeasAux_ptr, cplexDualSlaveFeasAux_ptr);//Solve Aux DSP to get the extreme point, which is extreme ray for Classical DSP.
			//	if (status != 0) {
			//		Found_Error("Solve_Dual_Slave");
			//		return -1;
			//	}
			//	DualStatus = cplexDualSlaveFeasAux_ptr.getStatus();
			//	FeasAuxDualSlaveObjFunction = cplexDualSlaveFeasAux_ptr.getObjValue();
			//	if (FeasAuxDualSlaveObjFunction < LowestFeasAuxDualSlaveObjFunction && FeasAuxDualSlaveObjFunction>1) {
			//		LowestFeasAuxDualSlaveObjFunction = FeasAuxDualSlaveObjFunction;
			//		status = UpdateDualSlaveFeasAuxCon();
			//		if (status != 0) {
			//			Found_Error("UpdateDualSlaveFeasAuxCon");
			//			return -1;
			//		}

			//	}
			//	if (DualStatus == 2) { //---------IF DUAL SLAVE IS FEASIBLE-----
			//		IloExpr expr102(env);
			//		status = CreateBendersCut(0, expr102);//if =1, then creates optimality cut
			//		if (status != 0) {
			//			Found_Error("CreateBendersFeasibilityCut");
			//			return -1;
			//		}
			//		FromFeasAux = true;
			//		FromAux = false;
			//		status = AddBendersCutToMaster(0, expr102, loop, modelMaster_ptr, FromAux, FromFeasAux);//if =1, then adds optimality cut
			//		if (status != 0) {
			//			Found_Error("AddBendersFeasibilityCutToMaster");
			//			return -1;
			//		}
			//		expr102.end();
			//	}
			//}
			//else 
			if (FoundFeasibleSolution == true && SameMasterSolution == false && NeedClassicalDSP == false) {
				//----------SOLVE THE AUXILIARY DUAL SLAVE PROBLEM AND ADD CUT TO MASTER
				status = UpdateDualSlaveObjective(Dual_objective_Aux);
				if (status != 0) {
					Found_Error("UpdateDualSlaveObjective");
					return -1;
				}

				/*status = UpdateDualSlaveAuxCon(&FirstTime, loop, &NoOfTimes, modelDualSlaveAux_ptr);
				if (status != 0) {
					Found_Error("UpdateDualSlaveAuxCon");
					return -1;
				}*/


				status = Solve_Dual_Slave(modelDualSlaveAux_ptr, cplexDualSlaveAux_ptr);
				if (status != 0) {
					Found_Error("Solve_Dual_Slave_Aux");
					return -1;
				}

				DualStatus = cplexDualSlaveAux_ptr.getStatus();
				if (DualStatus == 3) {//---------IF DUAL SLAVE IS INFEASIBLE-----
					break;
				}

				if (DualStatus == 4) { //---------IF AUXILIARY DUAL SLAVE IS UNBOUNDED-----

					status = Aux_Dual_Slave_Unbounded(&AuxDualSlaveObjFunction, &AuxPrimalSlaveObjFunction);
					if (status != 0) {
						Found_Error("AuxDual_Slave_Unbounded");
						return -1;
					}

					status = GetExtremeRayOfDSP(cplexDualSlaveAux_ptr);
					if (status != 0) {
						Found_Error("GetExtremeRayOfDSP");
						return -1;
					}

					IloExpr expr101(env);
					status = CreateBendersCut(0, expr101);//if =0, then creates feasibility cut
					if (status != 0) {
						Found_Error("CreateBendersFeasibilityCut");
						return -1;
					}
					FromFeasAux = false;
					FromAux = true;
					status = AddBendersCutToMaster(0, expr101, loop, modelMaster_ptr, FromAux, FromFeasAux);//if =0, then adds feasibility cut
					if (status != 0) {
						Found_Error("AddBendersFeasibilityCutToMaster");
						return -1;
					}
					expr101.end();

				}//Fin de IF QUI A TROUVE QUE SLAVE 1 EST INFEASIBLE

				else { //------------- IF AUXILIARY DUAL SLAVE PROBLEM IS BOUNDED------------

					status = Aux_Dual_Slave_Bounded(cplexDualSlaveAux_ptr, &DTransposeY, &AuxDualSlaveObjFunction, &AuxPrimalSlaveObjFunction, &FirstTime, loop, &NoOfTimes, modelDualSlaveAux_ptr, NoofTimesWorseSolutionFound);
					if (status != 0) {
						Found_Error("Dual_Slave_Bounded");
						return -1;
					}


					/*status = GetExtremePointOfDSP(cplexDualSlaveAux_ptr);
					if (status != 0) {
						Found_Error("GetExtremePointOfDSP");
						return -1;
					}*/

					IloExpr expr101(env);
					status = CreateBendersCut(1, expr101);//if =1, then creates optimality cut
					if (status != 0) {
						Found_Error("CreateBendersOptimalityCut");
						return -1;
					}
					FromFeasAux = false;
					FromAux = true;
					status = AddBendersCutToMaster(1, expr101, loop, modelMaster_ptr, FromAux, FromFeasAux);//if =1, then adds optimality cut
					if (status != 0) {
						Found_Error("AddBendersOptimalityCutToMaster");
						return -1;
					}
					expr101.end();

				}
			}
			else {//------GET THE FEASIBILITY CUT FROM CLASSICAL DSP
				status = GetExtremeRayOfDSP(cplexDualSlave_ptr);
				if (status != 0) {
					Found_Error("GetExtremeRayOfDSP");
					return -1;
				}

				IloExpr expr101(env);
				status = CreateBendersCut(0, expr101);//if =0, then creates feasibility cut
				if (status != 0) {
					Found_Error("CreateBendersFeasibilityCut");
					return -1;
				}
				FromFeasAux = false;
				FromAux = false;
				status = AddBendersCutToMaster(0, expr101, loop, modelMaster_ptr, FromAux, FromFeasAux);//if =0, then adds feasibility cut
				if (status != 0) {
					Found_Error("AddBendersFeasibilityCutToMaster");
					return -1;
				}
				expr101.end();
				//end of if(OptimalDualSlaveObjFunction==100){//if we haven't found a feasible solution yet
			}
		}
		else { //------------- IF CLASSICAL DUAL SLAVE PROBLEM IS BOUNDED------------

			status = Dual_Slave_Bounded(cplexDualSlave_ptr, &DTransposeY, &DualSlaveObjFunction, &PrimalSlaveObjFunction, &FirstTime, loop, &NoOfTimes, modelDualSlaveAux_ptr, NoofTimesWorseSolutionFound);
			if (status != 0) {
				Found_Error("Dual_Slave_Bounded");
				return -1;
			}
			FoundFeasibleSolution = true;
			NeedClassicalDSP = false;
			if (SameMasterSolution == false && NeedClassicalDSP == false) {//if we haven't found a feasible solution yet
																		   //----------SOLVE THE AUXILIARY DUAL SLAVE PROBLEM AND ADD CUT TO MASTER
				status = UpdateDualSlaveObjective(Dual_objective_Aux);
				if (status != 0) {
					Found_Error("UpdateDualSlaveObjective");
					return -1;
				}

				/*status = UpdateDualSlaveAuxCon(&FirstTime, loop, &NoOfTimes, modelDualSlaveAux_ptr);
				if (status != 0) {
					Found_Error("UpdateDualSlaveAuxCon");
					return -1;
				}*/

				status = Solve_Dual_Slave(modelDualSlaveAux_ptr, cplexDualSlaveAux_ptr);
				if (status != 0) {
					Found_Error("Solve_Dual_Slave_Aux");
					return -1;
				}

				DualStatus = cplexDualSlaveAux_ptr.getStatus();
				if (DualStatus == 3) {//---------IF DUAL SLAVE IS INFEASIBLE-----
					break;
				}

				if (DualStatus == 4) { //---------IF AUXILIARY DUAL SLAVE IS UNBOUNDED-----

					status = Aux_Dual_Slave_Unbounded(&AuxDualSlaveObjFunction, &AuxPrimalSlaveObjFunction);
					if (status != 0) {
						Found_Error("AuxDual_Slave_Unbounded");
						return -1;
					}

					status = GetExtremeRayOfDSP(cplexDualSlaveAux_ptr);
					if (status != 0) {
						Found_Error("GetExtremeRayOfDSP");
						return -1;
					}

					IloExpr expr101(env);
					status = CreateBendersCut(0, expr101);//if =0, then creates feasibility cut
					if (status != 0) {
						Found_Error("CreateBendersFeasibilityCut");
						return -1;
					}
					FromFeasAux = false;
					FromAux = true;
					status = AddBendersCutToMaster(0, expr101, loop, modelMaster_ptr, FromAux, FromFeasAux);//if =0, then adds feasibility cut
					if (status != 0) {
						Found_Error("AddBendersFeasibilityCutToMaster");
						return -1;
					}
					expr101.end();

				}//Fin de IF QUI A TROUVE QUE SLAVE 1 EST INFEASIBLE

				else { //------------- IF AUXILIARY DUAL SLAVE PROBLEM IS BOUNDED------------

					status = Aux_Dual_Slave_Bounded(cplexDualSlaveAux_ptr, &DTransposeY, &AuxDualSlaveObjFunction, &AuxPrimalSlaveObjFunction, &FirstTime, loop, &NoOfTimes, modelDualSlaveAux_ptr, NoofTimesWorseSolutionFound);
					if (status != 0) {
						Found_Error("Dual_Slave_Bounded");
						return -1;
					}


					/*status = GetExtremePointOfDSP(cplexDualSlaveAux_ptr);
					if (status != 0) {
						Found_Error("GetExtremePointOfDSP");
						return -1;
					}*/

					IloExpr expr101(env);
					status = CreateBendersCut(1, expr101);//if =1, then creates optimality cut
					if (status != 0) {
						Found_Error("CreateBendersOptimalityCut");
						return -1;
					}
					FromFeasAux = false;
					FromAux = true;
					status = AddBendersCutToMaster(1, expr101, loop, modelMaster_ptr, FromAux, FromFeasAux);//if =1, then adds optimality cut
					if (status != 0) {
						Found_Error("AddBendersOptimalityCutToMaster");
						return -1;
					}
					expr101.end();

				}

			}
			else {//-----GET THE OPTIMALITY CUT FROM THE CLASSICAL DSP
				IloExpr expr101(env);
				status = CreateBendersCut(1, expr101);//if =1, then creates optimality cut
				if (status != 0) {
					Found_Error("CreateBendersOptimalityCut");
					return -1;
				}
				FromFeasAux = false;
				FromAux = false;
				status = AddBendersCutToMaster(1, expr101, loop, modelMaster_ptr, FromAux, FromFeasAux);//if =1, then adds optimality cut
				if (status != 0) {
					Found_Error("AddBendersOptimalityCutToMaster");
					return -1;
				}
				expr101.end();
			}
		}//end of else if (ClassicalDualStatus==4)

		SameCut = true;
		vector <double> FormerId;
		vector <double> LatterId;
		vector <double> FormerCoef;
		vector <double> LatterCoef;
		FormerId.clear();
		LatterId.clear();
		FormerCoef.clear();
		LatterCoef.clear();

		//if (OptimalDualSlaveObjFunction<100){
		if (loop > 2) {
			for (IloExpr::LinearIterator former = IloExpr(BendersCuts[loop - 2].getExpr()).getLinearIterator(); former.ok(); ++former) {
				FormerId.push_back(former.getVar().getId());
				FormerCoef.push_back(former.getCoef());
			}

			for (IloExpr::LinearIterator latter = IloExpr(BendersCuts[loop - 1].getExpr()).getLinearIterator(); latter.ok(); ++latter) {
				LatterId.push_back(latter.getVar().getId());
				LatterCoef.push_back(latter.getCoef());
			}
			double MinSize = FormerId.size();
			if (MinSize > LatterId.size()) {
				MinSize = LatterId.size();
			}
			for (i = 0; i < MinSize; i++) {
				if (FormerId.at(i) != LatterId.at(i)) {
					SameCut = false;
				}
				else {
					if (FormerCoef.at(i) != LatterCoef.at(i)) {
						SameCut = false;
						//}else{
						//cout << "latter var: "<< LatterId.at(i) << " former var: "<< FormerId.at(i) << endl;
						//cout << "latter coef: "<< LatterCoef.at(i) << " former coef: "<< FormerCoef.at(i) << endl;
					}
				}
			}
			if (FormerId.size() != LatterId.size()) {
				SameCut = false;
			}
		}
		//}


		if (SameCut == true && FoundFeasibleSolution == true) {
			NeedClassicalDSP = true;
			cout << "SAME CUT PRODUCED" << endl;
			NoOfSameCuts++;
		}



		//if(BendersCuts[loop-1].getExpr().==BendersCuts[loop-2].getExpr().asNumExpr()){
		//OptimalDualSlaveObjFunction=100;
		//}

		duration = (long double)(clock() - start) / CLOCKS_PER_SEC;
		cTx.push_back(PrimalSlaveObjFunction);
		bTu.push_back(DualSlaveObjFunction);
		cTxAux.push_back(AuxPrimalSlaveObjFunction);
		bTuAux.push_back(AuxDualSlaveObjFunction);
		BestPrimalSlaveObjSoFar.push_back(OptimalPrimalSlaveObjFunction);
		BestDualSlaveObjSoFar.push_back(OptimalDualSlaveObjFunction);
		LowerBoundArray.push_back(LowerBound);
		UpperBoundArray.push_back(UpperBound);
		UpperBoundGlobalArray.push_back(UpperBoundGlobal);
		UpperBoundAuxArray.push_back(UpperBoundAux);
		UpperBoundGlobalAuxArray.push_back(UpperBoundGlobalAux);
		Time.push_back(duration);
		NoOfCutsInEachIteration.push_back(CutsPerIteration);
		Gap = (UpperBoundGlobal - LowerBound) / UpperBoundGlobal;
		/*
		if(ThetaValue!=0){
		cout<<"OptimalThetaValue="<<OptimalThetaValue<<endl;
		}
		if(DTransposeY!=0){
		cout<<"DTransposeY="<<DTransposeY<<endl;
		}
		if(SlaveObjFunction!=0){
		cout<<"SlaveObjFunction="<<SlaveObjFunction<<endl;
		}
		if(OptimalSlaveObjFunction!=0){
		cout<<"OptimalSlaveObjFunction="<<OptimalSlaveObjFunction<<endl;
		}
		*/
		cout << "LowerBound=" << LowerBound << endl;
		cout << "UpperBoundGlobal=" << UpperBoundGlobal << endl;
		cout << "Gap=" << Gap * 100 << "%" << endl;
		//cout << "SameCut=" << SameCut << endl;
		//cout << "SameMasterSolution=" << SameMasterSolution << endl;

		SameCutVector.push_back(SameCut);
		SameMasterSolutionVector.push_back(SameMasterSolution);
		//cout<<"UpperBound="<<UpperBound<<endl;

		//std::ostringstream UValues;
		//UValues << "C:\\Results_CrudeOil\\BDAux&FeasAux(DUAL)\\BDAux&FeasAux(DUAL)(i" << imax << ",z" << zmax << ",k" << kmax << ",j" << jmax << ",t" << tmax << ")\\BDAux&FeasAux(DUAL) - UValues.txt";
		//std::string FileNameUV = UValues.str();
		//std::ofstream fsUValues;
		//fsUValues.open(FileNameUV.c_str(), std::ios::app);
		//fsUValues << "Iteration" << loop << "\t";
		//for (i = 0; i < imax; i++) {
		//	for (j = 0; j < jmax; j++) {
		//		for (t = 0; t < tmax; t++) {
		//			fsUValues << U1Valueijt[i][j][t] << "\t";
		//		}
		//	}
		//}
		//for (k = 0; k < kmax; k++) {
		//	for (j = 0; j < jmax; j++) {
		//		for (t = 0; t < tmax; t++) {
		//			fsUValues << U2Valuekjt[k][j][t] << "\t";
		//		}
		//	}
		//}
		//for (z = 0; z < zmax; z++) {
		//	for (j = 0; j < jmax; j++) {
		//		for (t = 0; t < tmax; t++) {
		//			fsUValues << U3Valuezjt[z][j][t] << "\t";
		//			fsUValues << U9Valuezjt[z][j][t] << "\t";
		//			fsUValues << U10Valuezjt[z][j][t] << "\t";
		//		}
		//	}
		//}

		//for (z = 0; z < zmax; z++) {
		//	for (t = 0; t < tmax; t++) {
		//		fsUValues << U4Valuezt[z][t] << "\t";
		//	}
		//}

		//for (i = 0; i < imax; i++) {
		//	for (z = 0; z < zmax; z++) {
		//		for (t = 0; t < tmax; t++) {
		//			fsUValues << U5Valueizt[i][z][t] << "\t";
		//			fsUValues << U6Valueizt[i][z][t] << "\t";
		//			fsUValues << U11Valueizt[i][z][t] << "\t";
		//			fsUValues << U13Valueizt[i][z][t] << "\t";
		//		}
		//	}
		//}
		//for (k = 0; k < kmax; k++) {
		//	for (z = 0; z < zmax; z++) {
		//		for (t = 0; t < tmax; t++) {
		//			fsUValues << U7Valuekzt[k][z][t] << "\t";
		//			fsUValues << U8Valuekzt[k][z][t] << "\t";
		//			fsUValues << U12Valuekzt[k][z][t] << "\t";
		//			fsUValues << U14Valuekzt[k][z][t] << "\t";
		//		}
		//	}
		//}
		//fsUValues << std::endl;
		//fsUValues.close();


		////-----------Back-up Master Values-----------

		//std::ostringstream YValues;
		//YValues << "C:\\Results_CrudeOil\\BDAux&FeasAux(DUAL)\\BDAux&FeasAux(DUAL)(i" << imax << ",z" << zmax << ",k" << kmax << ",j" << jmax << ",t" << tmax << ")\\BDAux&FeasAux(DUAL) - YValues.txt";
		//std::string FileNameYV = YValues.str();
		//std::ofstream fsYValues;
		//fsYValues.open(FileNameYV.c_str(), std::ios::app);
		//fsYValues << "Iteration" << loop << "\t";
		//for (i = 0; i < imax; i++) {
		//	for (z = 0; z < zmax; z++) {
		//		for (t = 0; t < tmax; t++) {
		//			fsYValues << CiztValue[i][z][t] << "\t";
		//		}
		//	}
		//}
		//for (k = 0; k < kmax; k++) {
		//	for (z = 0; z < zmax; z++) {
		//		for (t = 0; t < tmax; t++) {
		//			fsYValues << DkztValue[k][z][t] << "\t";
		//		}
		//	}
		//}
		//for (z = 0; z < zmax; z++) {
		//	for (j = 0; j < jmax; j++) {
		//		for (t = 0; t < tmax; t++) {
		//			fsYValues << FzjtValue[z][j][t] << "\t";
		//		}
		//	}
		//}

		//for (n = 0; n < 1; n++) {
		//	fsYValues << ThetaValue << "\t";
		//}
		//fsYValues << std::endl;
		//fsYValues.close();


		//-------FINISH of Back-up Master Values







		cout << "-----------------" << endl;
		cout << "------END OF ITERATION--------" << endl;

	}//end of loop
	*loop_iter = loop;
	return 0;
}//end of BendersIteration

int PrintOptimalSolution(char* FilePath_Results_ptr, int loop_iter, int NoofTimesWorseSolutionFound) {
	int status, test = 0;
	char* FileName_ptr;
	char filepath[1024];
	char FileName_Problem_ptr[18];
	if (FileName_Problem[34] == 't') {
		memcpy(FileName_Problem_ptr, &FileName_Problem[14], 17);
		FileName_Problem_ptr[17] = '\0';
	}
	else {
		memcpy(FileName_Problem_ptr, &FileName_Problem[14], 16);
		FileName_Problem_ptr[16] = '\0';
	}


	//cout << FileName_Problem_ptr << endl;
	sprintf(filepath, "%s/%s", FilePath_Results_ptr, FileName_Problem_ptr);
	//string stringpath = filepath;
	status = mkdir(filepath);
	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_OptimalSolution.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);



	outfile << FileName_Problem_ptr << std::endl;
	outfile << "TotalSolutionTime= " << duration << " seconds " << std::endl;
	if ((UpperBoundGlobal - LowerBound) / UpperBoundGlobal > 0) {
		outfile << "OptimalityGap= " << (UpperBoundGlobal - LowerBound) / UpperBoundGlobal << std::endl;
	}
	else {
		outfile << "OptimalityGap= 0" << std::endl;
	}
	outfile << "OptimalObjFunction= " << OptimalOriginalObjFunction << std::endl;
	outfile << "TotalBendersIterations= " << loop_iter << std::endl;
	outfile << "NoofTimesWorseSolutionFound= " << NoofTimesWorseSolutionFound << std::endl;
	outfile << "----------------------------------" << std::endl;
	outfile << "TotalNumberOfFeasibilityCuts= " << BDFeasCuts << std::endl;
	outfile << "TotalNumberOfOptimalityCuts= " << BDOptCuts << std::endl;
	outfile << "FeasibilityCutsFromAuxiliaryProblem= " << BDFeasCutsFromAux << std::endl;
	outfile << "OptimalityCutsFromAuxiliaryProblem= " << BDOptCutsFromAux << std::endl;
	outfile << "----------------------------------" << std::endl;
	outfile << "SameCutsProduced= " << NoOfSameCuts << std::endl;
	outfile << "SameMasterSolutionProduced= " << NoOfSameMasterSolution << std::endl;
	outfile << "----------------------------------" << std::endl;
	outfile << "FeasibilityCutsFromFeasAuxiliaryProblem= " << BDFeasCutsFromFeasAux << std::endl;
	outfile << "OptimalityCutsFromFeasAuxiliaryProblem= " << BDOptCutsFromFeasAux << std::endl;
	outfile << "TotalNumberOfMasterVariables= " << NoOfMasterVars << std::endl;
	outfile << "TotalNumberOfSlaveVariables= " << NoOfSlaveVars << std::endl;
	outfile << "TotalNumberOfMasterConstraints= " << NoOfMasterCons << std::endl;
	outfile << "TotalNumberOfSlaveConstraints= " << NoOfSlaveCons << std::endl;
	outfile << "----------------------------------" << std::endl;
	outfile << "OptimalMasterObjFunction= " << OptimalMasterObjFunction << std::endl;
	outfile << "OptimalPrimalSlaveObjFunction= " << OptimalPrimalSlaveObjFunction << std::endl;
	outfile << "OptimalDualSlaveObjFunction= " << OptimalDualSlaveObjFunction << std::endl;
	outfile << "----------------------------------" << std::endl;
	if (OptimalThetaValue > 0.01) {
		outfile << "OptimalThetaValue= " << OptimalThetaValue << std::endl;
	}
	outfile << "----------------------------------" << std::endl;

	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				if (OptimalCiztValue[i][z][t] >= 0.01) {
					outfile << "OptimalCiztValue" << "[" << i << "]" << "[" << z << "]" << "[" << t << "]" << "=" << OptimalCiztValue[i][z][t] << std::endl;
				}
			}
		}
	}
	outfile << "----------------------------------" << std::endl;

	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				if (OptimalDkztValue[k][z][t] >= 0.01) {
					outfile << "OptimalDkztValue" << "[" << k << "]" << "[" << z << "]" << "[" << t << "]" << "=" << OptimalDkztValue[k][z][t] << std::endl;
				}
			}
		}
	}
	outfile << "----------------------------------" << std::endl;

	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				if (OptimalFzjtValue[z][j][t] >= 0.01) {
					outfile << "OptimalFzjtValue" << "[" << z << "]" << "[" << j << "]" << "[" << t << "]" << "=" << OptimalFzjtValue[z][j][t] << std::endl;
				}
			}
		}
	}
	outfile << "----------------------------------" << std::endl;

	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				if (OptimalSCiztValue[i][z][t] >= 0.01) {
					outfile << "OptimalSCiztValue" << "[" << i << "]" << "[" << z << "]" << "[" << t << "]" << "=" << OptimalSCiztValue[i][z][t] << std::endl;
				}
			}
		}
	}
	outfile << "----------------------------------" << std::endl;

	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				if (OptimalSDkztValue[k][z][t] >= 0.01) {
					outfile << "OptimalSDkztValue" << "[" << k << "]" << "[" << z << "]" << "[" << t << "]" << "=" << OptimalSDkztValue[k][z][t] << std::endl;
				}
			}
		}
	}
	outfile << "----------------------------------" << std::endl;

	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			for (j = 0; j < jmax; j++) {
				for (t = 0; t < tmax; t++) {
					if (OptimalXizjtValue[i][z][j][t] >= 0.01) {
						outfile << "OptimalXizjtValue" << "[" << i << "]" << "[" << z << "]" << "[" << j << "]" << "[" << t << "]" << "=" << OptimalXizjtValue[i][z][j][t] << std::endl;
					}
				}
			}
		}
	}
	outfile << "----------------------------------" << std::endl;

	for (z = 0; z < zmax; z++) {
		for (k = 0; k < kmax; k++) {
			for (j = 0; j < jmax; j++) {
				for (t = 0; t < tmax; t++) {
					if (OptimalYzkjtValue[z][k][j][t] >= 0.01) {
						outfile << "OptimalYzkjtValue" << "[" << z << "]" << "[" << k << "]" << "[" << j << "]" << "[" << t << "]" << "=" << OptimalYzkjtValue[z][k][j][t] << std::endl;
					}
				}
			}
		}
	}
	outfile << "----------------------------------" << std::endl;


	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			for (t = 0; t < tmax; t++) {
				if (OptimalIzjtValue[z][j][t] >= 0.01) {
					outfile << "OptimalIzjtValue" << "[" << z << "]" << "[" << j << "]" << "[" << t << "]" << "=" << OptimalIzjtValue[z][j][t] << std::endl;
				}
			}
		}
	}

	outfile.close();


	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_LowerBound.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < LowerBoundArray.size(); i++) {
		outfile << LowerBoundArray.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_UpperBound.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < UpperBoundArray.size(); i++) {
		outfile << UpperBoundArray.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_UpperBoundGlobal.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < UpperBoundGlobalArray.size(); i++) {
		outfile << UpperBoundGlobalArray.at(i) << std::endl;
	}
	outfile.close();

	/*sprintf(filepath, "%s/%s/%s_BENDERS_LowerBoundGlobal.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < LowerBoundGlobalArray.size(); i++) {
		outfile << LowerBoundGlobalArray.at(i) << std::endl;
	}
	outfile.close();*/


	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_UpperBoundAux.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < UpperBoundAuxArray.size(); i++) {
		outfile << UpperBoundAuxArray.at(i) << std::endl;
	}
	outfile.close();


	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_UpperBoundGlobalAux.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < UpperBoundGlobalAuxArray.size(); i++) {
		outfile << UpperBoundGlobalAuxArray.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_dTransY.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < dTy.size(); i++) {
		outfile << dTy.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_cTransX.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < cTx.size(); i++) {
		outfile << cTx.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_bTransU.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < bTu.size(); i++) {
		outfile << bTu.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_cTransXAux.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < cTxAux.size(); i++) {
		outfile << cTxAux.at(i) << std::endl;
	}
	outfile.close();


	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_bTransUAux.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < bTuAux.size(); i++) {
		outfile << bTuAux.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_CurrentHeta.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < zCurrent.size(); i++) {
		outfile << zCurrent.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_BestPrimalSlaveObjSoFar.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < BestPrimalSlaveObjSoFar.size(); i++) {
		outfile << BestPrimalSlaveObjSoFar.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_BestDualSlaveObjSoFar.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < BestDualSlaveObjSoFar.size(); i++) {
		outfile << BestDualSlaveObjSoFar.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_TimePath.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < Time.size(); i++) {
		outfile << Time.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_SlackValuesBendersCuts.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	i = 0;//No. of slack values
	j = 0;//No. of iterations
	k = 0;//Index of slack values
	while (j < NoOfCutsInEachIteration.size()) {//for each iteration
		z = 0;
		k += NoOfCutsInEachIteration.at(j);
		while (i < SlackValuesOfBendersCuts.size() && z < k) {//for each slack value
			outfile << SlackValuesOfBendersCuts.at(i) << "\t";
			z++;
			i++;
		}
		outfile << std::endl;
		j++;
	}
	outfile.close();



	cout << "Max size of vector SlackValuesOfMainMasterCons=" << SlackValuesOfMainMasterCons.max_size() << endl;
	cout << "Current size of vector SlackValuesOfMainMasterCons=" << SlackValuesOfMainMasterCons.size() << endl;

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_SlackValuesMainMasterCons.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < SlackValuesOfMainMasterCons.size(); i++) {
		outfile << SlackValuesOfMainMasterCons.at(i) << "\t";
		if ((i + 1) % NoOfMasterCons == 0) {
			outfile << std::endl;
		}
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_SameCut.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < SameCutVector.size(); i++) {
		outfile << SameCutVector.at(i) << std::endl;
	}
	outfile.close();


	sprintf(filepath, "%s/%s/%s_BDAux(DUAL)_SameMasterSolution.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < SameMasterSolutionVector.size(); i++) {
		outfile << SameMasterSolutionVector.at(i) << std::endl;
	}
	outfile.close();

	return 0;
}

int main(int argc, char **argv)
{
	int  stop, status;

	std::ostringstream oss;
	oss << "Crude_Oil_Data(i" << imax << ",z" << zmax << ",k" << kmax << ",j" << jmax << ",t" << tmax << ").txt";
	std::string ProblemName = oss.str();
	//string ProblemName = "Crude_Oil_Data(i"<<i<<", z"<<z<<", k"<<k<<", j"<<j<<", t"<<t<<").txt";
	strcpy(FileName_Problem, ProblemName.c_str());
	cout << FileName_Problem << endl;
	//FileName_Problem = "Crude_Oil_Data(i1, z6, k2, j3, t4).txt";


	status = load_data(FilePath_Data);
	if (status != 0) {
		Found_Error("load_data");
		return -1;
	}
	start = clock();
	status = do_master();
	if (status != 0) {
		Found_Error("do_master");
		return -1;
	}

	status = do_dual_slave_and_aux();
	if (status != 0) {
		Found_Error("do_dual_slave_and_aux");
		return -1;
	}

	/*status = do_dual_FeasAux();
	if (status != 0) {
		Found_Error("do_dual_FeasAux");
		return -1;
	}*/
	int loop_iter = 0, NoofTimesWorseSolutionFound = 0;
	status = BendersIteration(modelMaster, modelDualSlave, modelDualSlaveAux, modelDualSlaveFeasAux, &loop_iter, &NoofTimesWorseSolutionFound);
	if (status != 0) {
		Found_Error("BendersIteration");
		return -1;
	}
	stop = clock();
	duration = (long double)(stop - start) / CLOCKS_PER_SEC;

	status = PrintOptimalSolution(FilePath_Results, loop_iter, NoofTimesWorseSolutionFound);
	if (status != 0) {
		Found_Error("PrintOptimalSolution");
		return -1;
	}

	env.end();

	printf("Code terminated successfully \n");
	printf("Execution time = %Lf seconds\n", duration);
	printf("Same Cuts produced = %d \n", NoOfSameCuts);

	return 0;

} //End main