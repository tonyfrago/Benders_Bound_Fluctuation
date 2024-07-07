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
int tmax, zmax, imax, kmax, jmax;
const int capmax = 100000;
const int capmin = 0;
const int BigM = 100000;
double **E_it;
double ***ae_ijt;
double **S_kt;
double ***as_kjt;
double **initial_zj;

//Parameters affecting solution
double epsilon = 0.001;
double UpperBound = 100;
double LowerBound = 0;
double UpperBoundGlobal = 100;
double fraction = 0.90;
long double duration;  // tracks time
int start = 0, BDFeasCuts = 0, BDOptCuts = 0, CutsPerIteration, NoOfMasterVariables = 0, NoOfMasterCons = 0;
double Gap = 1;
int SolutionStatus;


double ***CiztValue;
double ***DkztValue;
double ***FzjtValue;
double ***SCiztValue;
double ***SDkztValue;
double ****XizjtValue;
double ****YzkjtValue;
double ***IzjtValue;
double ThetaValue = 0;

double ***OptimalCiztValue;
double ***OptimalDkztValue;
double ***OptimalFzjtValue;
double ***OptimalSCiztValue;
double ***OptimalSDkztValue;
double ****OptimalXizjtValue;
double ****OptimalYzkjtValue;
double ***OptimalIzjtValue;
double OptimalThetaValue = 0;

double OptimalOriginalObjFunction = 0;
double OptimalMasterObjFunction = 0;
double OptimalSlaveObjFunction = 0;

ifstream infile;
ofstream outfile, solution, solution_results, solution1, solution_results1;
char* FilePath_DataSet = "C:/PhD_Examples/Data_CrudeOil";//C:/PhD_Examples //G:/Antonis/PhD_Examples
char* FilePath_Data = "C:/PhD_Examples/Data_CrudeOil";
char* FilePath_Results = "C:/PhD_Examples/Results_CrudeOil/CPLEX";//G:/Antonis/PhD_Examples
//char* FilePath_Results_FileName = "BENDERS";
char FileName_DataSet[512] = "DataSet";
char FileName_DataSetIndices[512] = "DataSetIndices";
const int TotalNoOfProblems = 10;
string ProblemNames[TotalNoOfProblems];
char FileName_Problem[512];
int imaxset[TotalNoOfProblems], zmaxset[TotalNoOfProblems], kmaxset[TotalNoOfProblems], jmaxset[TotalNoOfProblems], tmaxset[TotalNoOfProblems];


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

//--------Declare dual variables of each constraint----------------

//double valsDualCT3Melzt[zmax][tmax];

double ***S2valsDualSumXijt;
double ***S2valsDualSumYkjt;
double ***S2valsDualCTIzjt;

double ***S22valsDualSumXijt;
double ***S22valsDualSumYkjt;
double ***S22valsDualCTIzjt;

double **S2valsDualSum_Izt;

double ***S2valsDualCT1Fonctionement_Cizt;
double ***S2valsDualCT2Fonctionement_Cizt;
double ***S2valsDualCT1Fonctionement_Dkzt;
double ***S2valsDualCT2Fonctionement_Dkzt;

double ***S2valsDualCT1Melzjt;
double ***S2valsDualCT2Melzjt;

double ***S2valsDualSC2_Cizt;
double ***S2valsDualSD2_Dkzt;
double ***S2valsDualSC_Cizt;
double ***S2valsDualSD_Dkzt;



vector <double> LowerBoundArray;
vector <double> UpperBoundArray;
vector <double> UpperBoundGlobalArray;
vector <double> dTy;
vector <double> zCurrent;
vector <double> cTx;
vector <double> BestSlaveObjSoFar;
vector <double> Time;
vector <double> SlackValuesOfBendersCuts;
vector <double> NoOfCutsInEachIteration;
vector <double> NoOfCoveredVarsInEachIteration;


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
double InsertDataSet(char* FilePath_Data_ptr) {
	char filepath[1024];
	sprintf(filepath, "%s/%s.txt", FilePath_Data_ptr, FileName_DataSet);
	infile.open(filepath);
	/////////////////F:\Dropbox\GreenYourRoute Saharidis\GYR Saharidis\Algorithm\DATA nominal example
	//infile.open("C:/Users/zoigr/Dropbox/GYR UTH_EA/Actions/Action B2/Zoi - Action B2/TSP/3 Distance Data.txt");
	if (infile.fail()) {
		cout << "DataSet file could not be opened. Try correcting the file's location path." << endl;
		cout << filepath << endl;
		system("pause");
		exit(1);
	}
	for (int i = 0; i < TotalNoOfProblems; i++) {
		infile >> ProblemNames[i];
		//infile >> Customers[i];
	}
	infile.close();
}
double InsertDataSetIndices(char* FilePath_Data_ptr) {
	char filepath[1024];
	sprintf(filepath, "%s/%s.txt", FilePath_Data_ptr, FileName_DataSetIndices);
	infile.open(filepath);
	/////////////////F:\Dropbox\GreenYourRoute Saharidis\GYR Saharidis\Algorithm\DATA nominal example
	//infile.open("C:/Users/zoigr/Dropbox/GYR UTH_EA/Actions/Action B2/Zoi - Action B2/TSP/3 Distance Data.txt");
	if (infile.fail()) {
		cout << "DataSetIndices file could not be opened. Try correcting the file's location path." << endl;
		cout << filepath << endl;
		system("pause");
		exit(1);
	}
	for (int i = 0; i < TotalNoOfProblems; i++) {
		infile >> imaxset[i];
		infile >> zmaxset[i];
		infile >> kmaxset[i];
		infile >> jmaxset[i];
		infile >> tmaxset[i];
	}
	infile.close();
}
int AllocateMemory() {
	E_it = new double*[imax];
	S_kt = new double*[kmax];
	initial_zj = new double*[zmax];
	S2valsDualSum_Izt = new double*[zmax];
	for (i = 0; i < imax; i++) {
		E_it[i] = new double[tmax];
	}
	for (k = 0; k < kmax; k++) {
		S_kt[k] = new double[tmax];
	}
	for (z = 0; z < zmax; z++) {
		initial_zj[z] = new double[jmax];
	}
	for (t = 0; t < tmax; t++) {
		S2valsDualSum_Izt[z] = new double[tmax];
	}

	S2valsDualSumXijt = new double**[imax];
	S2valsDualSumYkjt = new double**[kmax];
	S22valsDualSumXijt = new double**[imax];
	S22valsDualSumYkjt = new double**[kmax];
	ae_ijt = new double**[imax];
	as_kjt = new double**[kmax];
	CiztValue = new double**[imax];
	SCiztValue = new double**[imax];
	S2valsDualCT1Fonctionement_Cizt = new double**[imax];
	S2valsDualCT2Fonctionement_Cizt = new double**[imax];
	S2valsDualSC2_Cizt = new double**[imax];
	S2valsDualSC_Cizt = new double**[imax];
	DkztValue = new double**[kmax];
	SDkztValue = new double**[kmax];
	S2valsDualCT1Fonctionement_Dkzt = new double**[kmax];
	S2valsDualCT2Fonctionement_Dkzt = new double**[kmax];
	S2valsDualSD2_Dkzt = new double**[kmax];
	S2valsDualSD_Dkzt = new double**[kmax];
	FzjtValue = new double**[zmax];
	IzjtValue = new double**[zmax];
	S2valsDualCTIzjt = new double**[zmax];
	S22valsDualCTIzjt = new double**[zmax];
	S2valsDualCT1Melzjt = new double**[zmax];
	S2valsDualCT2Melzjt = new double**[zmax];
	OptimalCiztValue = new double**[imax];
	OptimalSCiztValue = new double**[imax];
	OptimalDkztValue = new double**[kmax];
	OptimalSDkztValue = new double**[kmax];
	OptimalFzjtValue = new double**[zmax];
	OptimalIzjtValue = new double**[zmax];
	for (i = 0; i < imax; i++) {
		ae_ijt[i] = new double*[jmax];
		S2valsDualSumXijt[i] = new double*[jmax];
		S22valsDualSumXijt[i] = new double*[jmax];
		CiztValue[i] = new double*[zmax];
		SCiztValue[i] = new double*[zmax];
		S2valsDualCT1Fonctionement_Cizt[i] = new double*[zmax];
		S2valsDualCT2Fonctionement_Cizt[i] = new double*[zmax];
		S2valsDualSC2_Cizt[i] = new double*[zmax];
		S2valsDualSC_Cizt[i] = new double*[zmax];
		OptimalCiztValue[i] = new double*[zmax];
		OptimalSCiztValue[i] = new double*[zmax];
	}
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			ae_ijt[i][j] = new double[tmax];
			S2valsDualSumXijt[i][j] = new double[tmax];
			S22valsDualSumXijt[i][j] = new double[tmax];
		}
		for (z = 0; z < zmax; z++) {
			CiztValue[i][z] = new double[tmax];
			SCiztValue[i][z] = new double[tmax];
			S2valsDualCT1Fonctionement_Cizt[i][z] = new double[tmax];
			S2valsDualCT2Fonctionement_Cizt[i][z] = new double[tmax];
			S2valsDualSC2_Cizt[i][z] = new double[tmax];
			S2valsDualSC_Cizt[i][z] = new double[tmax];
			OptimalCiztValue[i][z] = new double[tmax];
			OptimalSCiztValue[i][z] = new double[tmax];
		}
	}
	for (k = 0; k < kmax; k++) {
		as_kjt[k] = new double*[jmax];
		S2valsDualSumYkjt[k] = new double*[jmax];
		S22valsDualSumYkjt[k] = new double*[jmax];
		DkztValue[k] = new double*[zmax];
		SDkztValue[k] = new double*[zmax];
		S2valsDualCT1Fonctionement_Dkzt[k] = new double*[zmax];
		S2valsDualCT2Fonctionement_Dkzt[k] = new double*[zmax];
		S2valsDualSD2_Dkzt[k] = new double*[zmax];
		S2valsDualSD_Dkzt[k] = new double*[zmax];
		OptimalDkztValue[k] = new double*[zmax];
		OptimalSDkztValue[k] = new double*[zmax];
	}
	for (k = 0; k < kmax; k++) {
		for (j = 0; j < jmax; j++) {
			as_kjt[k][j] = new double[tmax];
			S2valsDualSumYkjt[k][j] = new double[tmax];
			S22valsDualSumYkjt[k][j] = new double[tmax];
		}
		for (z = 0; z < zmax; z++) {
			DkztValue[k][z] = new double[tmax];
			SDkztValue[k][z] = new double[tmax];
			S2valsDualCT1Fonctionement_Dkzt[k][z] = new double[tmax];
			S2valsDualCT2Fonctionement_Dkzt[k][z] = new double[tmax];
			S2valsDualSD2_Dkzt[k][z] = new double[tmax];
			S2valsDualSD_Dkzt[k][z] = new double[tmax];
			OptimalDkztValue[k][z] = new double[tmax];
			OptimalSDkztValue[k][z] = new double[tmax];
		}
	}
	for (z = 0; z < zmax; z++) {
		FzjtValue[z] = new double*[jmax];
		IzjtValue[z] = new double*[jmax];
		S2valsDualCTIzjt[z] = new double*[jmax];
		S22valsDualCTIzjt[z] = new double*[jmax];
		S2valsDualCT1Melzjt[z] = new double*[jmax];
		S2valsDualCT2Melzjt[z] = new double*[jmax];
		OptimalFzjtValue[z] = new double*[jmax];
		OptimalIzjtValue[z] = new double*[jmax];
	}
	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			FzjtValue[z][j] = new double[tmax];
			IzjtValue[z][j] = new double[tmax];
			S2valsDualCTIzjt[z][j] = new double[tmax];
			S22valsDualCTIzjt[z][j] = new double[tmax];
			S2valsDualCT1Melzjt[z][j] = new double[tmax];
			S2valsDualCT2Melzjt[z][j] = new double[tmax];
			OptimalFzjtValue[z][j] = new double[tmax];
			OptimalIzjtValue[z][j] = new double[tmax];
		}
	}

	XizjtValue = new double***[imax];
	YzkjtValue = new double***[zmax];
	OptimalXizjtValue = new double***[imax];
	OptimalYzkjtValue = new double***[zmax];
	for (i = 0; i < imax; i++) {
		XizjtValue[i] = new double**[zmax];
		OptimalXizjtValue[i] = new double**[zmax];
	}
	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			XizjtValue[i][z] = new double*[jmax];
			OptimalXizjtValue[i][z] = new double*[jmax];
		}
	}
	for (z = 0; z < zmax; z++) {
		YzkjtValue[z] = new double**[kmax];
		OptimalYzkjtValue[z] = new double**[kmax];
	}
	for (z = 0; z < zmax; z++) {
		for (k = 0; k < kmax; k++) {
			YzkjtValue[z][k] = new double*[jmax];
			OptimalYzkjtValue[z][k] = new double*[jmax];
		}
	}

	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			for (j = 0; j < jmax; j++) {
				XizjtValue[i][z][j] = new double[tmax];
				OptimalXizjtValue[i][z][j] = new double[tmax];
			}
		}
	}
	for (z = 0; z < zmax; z++) {
		for (k = 0; k < kmax; k++) {
			for (j = 0; j < jmax; j++) {
				YzkjtValue[z][k][j] = new double[tmax];
				OptimalYzkjtValue[z][k][j] = new double[tmax];
			}
		}
	}

	return 0;
}

int load_data(char* FilePath_Data_ptr) {
	int status;
	char* FileName_ptr;
	char* FileName_ptr2;
	string read_file = "";
	status = AllocateMemory();
	if (status != 0) {
		Found_Error("AllocateMemory");
		return -1;
	}
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
	cout << "initial_zj" << endl;;
	for (z = 0; z < zmax; z++) {
		for (j = 0; j < jmax; j++) {
			infile >> initial_zj[z][j];
			cout << initial_zj[z][j] << '\t';
		}
		cout << endl;
	}
	infile.close();


	//E[0][0]=0;E[0][1]=0;E[0][2]=0;E[0][3]=120000;
	//ae[0][0][0]=0;ae[0][0][1]=0;ae[0][0][2]=0;ae[0][0][3]=1;
	//ae[0][1][0]=0;ae[0][1][1]=0;ae[0][1][2]=0;ae[0][1][3]=0;
	//ae[0][2][0]=0;ae[0][2][1]=0;ae[0][2][2]=0;ae[0][2][3]=0;
	//S[0][0]=0;S[0][1]=30000;S[0][2]=27750;S[0][3]=9750;
	//S[1][0]=0;S[1][1]=60000;S[1][2]=30000;S[1][3]=15600;
	//as[0][0][0]=0;as[0][0][1]=0.5;as[0][0][2]=1;as[0][0][3]=1;
	//as[0][1][0]=0;as[0][1][1]=0;as[0][1][2]=0;as[0][1][3]=0;
	//as[0][2][0]=0;as[0][2][1]=0.5;as[0][2][2]=0;as[0][2][3]=0;
	//as[1][0][0]=0;as[1][0][1]=0.41;as[1][0][2]=1;as[1][0][3]=0;
	//as[1][1][0]=0;as[1][1][1]=0;as[1][1][2]=0;as[1][1][3]=0;
	//as[1][2][0]=0;as[1][2][1]=0.59;as[1][2][2]=0;as[1][2][3]=1;
	//initial[0][0]=40000;initial[0][1]=0;initial[0][2]=0;
	//initial[1][0]=80000;initial[1][1]=0;initial[1][2]=0;
	//initial[2][0]=0;initial[2][1]=0;initial[2][2]=95000;
	//initial[3][0]=0;initial[3][1]=0;initial[3][2]=100000;
	//initial[4][0]=0;initial[4][1]=100000;initial[4][2]=0;
	//initial[5][0]=0;initial[5][1]=90000;initial[5][2]=0;
	//initial[6][0]=80000;initial[6][1]=0;initial[6][2]=0;
	//initial[7][0]=0;initial[7][1]=70000;initial[7][2]=0;

	for (z = 0; z < zmax; z++) {
		for (t = 0; t < tmax; t++) {
			for (i = 0; i < imax; i++) {
				CiztValue[i][z][t] = 0;
				SCiztValue[i][z][t] = 0;
				for (j = 0; j < jmax; j++) {
					XizjtValue[i][z][j][t] = 0;
					OptimalXizjtValue[i][z][j][t] = 0;
				}
			}
			for (k = 0; k < kmax; k++) {
				DkztValue[k][z][t] = 0;
				SDkztValue[k][z][t] = 0;
				for (j = 0; j < jmax; j++) {
					YzkjtValue[z][k][j][t] = 0;
					OptimalYzkjtValue[z][k][j][t] = 0;
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
int do_master(IloEnv env, IloModel modelMaster, IloNumVarMatrix3x3 Cizt, IloNumVarMatrix3x3 Dkzt, IloNumVarMatrix3x3 Fzjt, IloNumVarArray Zn, IloNumVarMatrix4x4 Xizjt, IloNumVarMatrix4x4 Yzkjt, IloNumVarMatrix3x3 Izjt, IloNumVarMatrix3x3 SCizt, IloNumVarMatrix3x3 SDkzt, IloRangeMatrix3x3 SumXijt, IloRangeMatrix3x3 DSumXijt, IloRangeMatrix3x3 SumYkjt, IloRangeMatrix3x3 DSumYkjt, IloRangeMatrix3x3 CTIzjt, IloRangeMatrix3x3 DCTIzjt, IloRangeMatrix2x2 Sum_Izt, IloRangeMatrix3x3 CT1Fonctionement_Cizt, IloRangeMatrix3x3 CT2Fonctionement_Cizt, IloRangeMatrix3x3 CT1Fonctionement_Dkzt, IloRangeMatrix3x3 CT2Fonctionement_Dkzt, IloRangeMatrix3x3 CT1Melzjt, IloRangeMatrix3x3 CT2Melzjt, IloRangeMatrix3x3 SC2_Cizt, IloRangeMatrix3x3 SD2_Dkzt, IloRangeMatrix3x3 SC_Cizt, IloRangeMatrix3x3 SD_Dkzt) {

	NoOfMasterVariables = 0;
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
				char Chargement[70];
				sprintf(Chargement, "Cizt(i%d,z%d,t%d)", i, z, t);
				IloNumVar C(env, 0, 1, ILOINT, Chargement);
				NoOfMasterVariables++;
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
				char Dechargement[70];
				sprintf(Dechargement, "Dkzt(k%d,z%d,t%d)", k, z, t);
				IloNumVar D(env, 0, 1, ILOINT, Dechargement);
				NoOfMasterVariables++;
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
				char variableF[70];
				sprintf(variableF, "Fzjt(z%d,j%d,t%d)", z, j, t);
				IloNumVar F(env, 0, 1, ILOINT, variableF);
				NoOfMasterVariables++;
				Ft.add(F);
			}
			Fjt.add(Ft);
		}
		Fzjt.add(Fjt);
	}


	//--------------------------- PRIMAL SLAVE PROBLEM ----------------------------------
	//------------------------------------------------------------------------------
	//--------------------------- Slave Primal Variables ---------------------------
	//--------------------------- Variable de Decision X ---------------------------

	for (i = 0; i < imax; i++) {
		IloNumVarMatrix3x3 Xzjt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarMatrix2x2 Xjt(env, 0);
			for (j = 0; j < jmax; j++) {
				IloNumVarArray Xt(env, 0);
				for (t = 0; t < tmax; t++) {
					char Quantite_Charge[70];
					sprintf(Quantite_Charge, "Xizjt(i%d,z%d,j%d,t%d)", i, z, j, t);
					IloNumVar X(env, 0, IloInfinity, ILOFLOAT, Quantite_Charge);
					NoOfMasterVariables++;
					Xt.add(X);
				}
				Xjt.add(Xt);
			}
			Xzjt.add(Xjt);
		}
		Xizjt.add(Xzjt);
	}
	//--------------------------- Variable de Decision Y --------------------------

	for (z = 0; z < zmax; z++) {
		IloNumVarMatrix3x3 Ykjt(env, 0);
		for (k = 0; k < kmax; k++) {
			IloNumVarMatrix2x2 Yjt(env, 0);
			for (j = 0; j < jmax; j++) {
				IloNumVarArray Yt(env, 0);
				for (t = 0; t < tmax; t++) {
					char Quantite_Decharge[70];
					sprintf(Quantite_Decharge, "Yzkjt(k%d,z%d,j%d,t%d)", k, z, j, t);
					IloNumVar Y(env, 0, IloInfinity, ILOFLOAT, Quantite_Decharge);
					NoOfMasterVariables++;
					Yt.add(Y);
				}
				Yjt.add(Yt);
			}
			Ykjt.add(Yjt);
		}
		Yzkjt.add(Ykjt);
	}
	//--------------------------- Variable de Decision I --------------------------

	for (z = 0; z < zmax; z++) {
		IloNumVarMatrix2x2 Ijt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloNumVarArray It(env, 0);
			for (t = 0; t < tmax; t++) {
				char Inventory[70];
				sprintf(Inventory, "Izjt(z%d,j%d,t%d)", z, j, t);
				IloNumVar I(env, 0, IloInfinity, ILOFLOAT, Inventory);
				NoOfMasterVariables++;
				It.add(I);
			}
			Ijt.add(It);
		}
		Izjt.add(Ijt);
	}

	//-------------- Variable de Decision SC ---------------------------------------

	for (i = 0; i < imax; i++) {
		IloNumVarMatrix2x2 SCzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray SCt(env, 0);
			for (t = 0; t < tmax; t++) {
				char SChargement[70];
				sprintf(SChargement, "SCizt(i%d,z%d,t%d)", i, z, t);
				IloNumVar SC(env, 0, IloInfinity, ILOFLOAT, SChargement);
				NoOfMasterVariables++;
				SCt.add(SC);
			}
			SCzt.add(SCt);
		}
		SCizt.add(SCzt);
	}
	//-------------- Variable de Decision SD ---------------------------------------

	for (k = 0; k < kmax; k++) {
		IloNumVarMatrix2x2 SDzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloNumVarArray SDt(env, 0);
			for (t = 0; t < tmax; t++) {
				char SDechargement[70];
				sprintf(SDechargement, "SDkzt(k%d,z%d,t%d)", k, z, t);
				IloNumVar SD(env, 0, IloInfinity, ILOFLOAT, SDechargement);
				NoOfMasterVariables++;
				SDt.add(SD);
			}
			SDzt.add(SDt);
		}
		SDkzt.add(SDzt);
	}

	//-----------------  FIN VARIABLE DE DECISION PRIMAL SLAVE 1 ------------------

	/*
	//--------------------------- Variable de Decision Z ---------------------------


	for (n=0;n<1;n++){
		char Theta[70];
		sprintf(Theta,"Zn(n%d)",n);
		IloNumVar Z(env,0,IloInfinity,ILOFLOAT,Theta);
		Zn.add(Z);
	}

	*/

	//-----------------------------Finish of Master Variables --------------------------------

	//-----------------------------------------------------------------------------
	//-------------------------Start of Master Constraints-----------------------------------------
	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//-------------------------- Contrainte de melange CT3 -------------------------
	IloRangeMatrix2x2 CT3Melzt(env, 0);
	for (z = 0; z < zmax; z++) {
		IloRangeArray CT3Melt(env, 0);
		for (t = 0; t < tmax; t++) {
			IloExpr expr(env, 0);
			for (j = 0; j < jmax; j++) {
				expr += Fzjt[z][j][t];
			}
			char CT3Melange[60];
			sprintf(CT3Melange, "CT3Melzjt(z%d,t%d)", z, t);
			double LBCT3Melzt = 0, UBCT3Melzt = 1;
			IloRange CT3Mel(env, LBCT3Melzt, expr, UBCT3Melzt, CT3Melange);
			NoOfMasterCons++;
			modelMaster.add(CT3Mel);
			CT3Melt.add(CT3Mel);
			expr.end();
		}
		CT3Melzt.add(CT3Melt);
	}

	//------------------------------- Chargement CT3 ---------------------------------
	IloRangeMatrix2x2 CT3C_ou_Dzt(env, 0);
	for (z = 0; z < zmax; z++) {
		IloRangeArray CT3C_ou_Dt(env, 0);
		for (t = 0; t < tmax; t++) {
			for (i = 0; i < imax; i++) {
				for (k = 0; k < kmax; k++) {
					IloExpr expr(env, 0);
					expr += Cizt[i][z][t] + Dkzt[k][z][t];
					char Chargement_ou_Dechargement[60];
					sprintf(Chargement_ou_Dechargement, "CT3C_ou_Dzt(z%d,t%d)", z, t);
					double LBCT3C_ou_Dzt = 0, UBCT3C_ou_Dzt = 1;
					IloRange CT3C_ou_D(env, LBCT3C_ou_Dzt, expr, UBCT3C_ou_Dzt, Chargement_ou_Dechargement);
					NoOfMasterCons++;
					modelMaster.add(CT3C_ou_D);
					CT3C_ou_Dt.add(CT3C_ou_D);
					expr.end();
				}
			}
		}
		CT3C_ou_Dzt.add(CT3C_ou_Dt);
	}

	//------------------------------- INITIAL VALUES (t=0) ---------------------------------
	//------------------------------- z tank contains j type at t=0 ---------------------------------
	IloRangeMatrix2x2 SupFzj0(env, 0);
	for (z = 0; z < zmax; z++) {
		IloRangeArray SupFj0(env, 0);
		for (j = 0; j < jmax; j++) {

			if (z == 0) {
				if (j == 0) {//------ 0 tank contains 0 type at t=0 ------------
					IloExpr expr(env, 0);
					expr = Fzjt[z][j][0];
					char ConSupFzj0[60];
					sprintf(ConSupFzj0, "ConSupFzj0(z%d,j%d)", z, j);
					double LB = 1, UB = 1;
					IloRange SupF0(env, LB, expr, UB, ConSupFzj0);
					NoOfMasterCons++;
					modelMaster.add(SupF0);
					SupFj0.add(SupF0);
					expr.end();
				}
				else {
					IloExpr expr(env, 0);
					expr = Fzjt[z][j][0];
					char ConSupFzj0[60];
					sprintf(ConSupFzj0, "ConSupFzj0(z%d,j%d)", z, j);
					double LB = 0, UB = 0;
					IloRange SupF0(env, LB, expr, UB, ConSupFzj0);
					NoOfMasterCons++;
					modelMaster.add(SupF0);
					SupFj0.add(SupF0);
					expr.end();
				}
			}


			if (z == 1) {
				if (j == 0) {//------ 1 tank contains 0 type at t=0 ------------
					IloExpr expr(env, 0);
					expr = Fzjt[z][j][0];
					char ConSupFzj0[60];
					sprintf(ConSupFzj0, "ConSupFzj0(z%d,j%d)", z, j);
					double LB = 1, UB = 1;
					IloRange SupF0(env, LB, expr, UB, ConSupFzj0);
					NoOfMasterCons++;
					modelMaster.add(SupF0);
					SupFj0.add(SupF0);
					expr.end();
				}
				else {
					IloExpr expr(env, 0);
					expr = Fzjt[z][j][0];
					char ConSupFzj0[60];
					sprintf(ConSupFzj0, "ConSupFzj0(z%d,j%d)", z, j);
					double LB = 0, UB = 0;
					IloRange SupF0(env, LB, expr, UB, ConSupFzj0);
					NoOfMasterCons++;
					modelMaster.add(SupF0);
					SupFj0.add(SupF0);
					expr.end();
				}
			}


			if (z == 2) {
				if (j == 2) {//------ 2 tank contains 2 type at t=0 ------------
					IloExpr expr(env, 0);
					expr = Fzjt[z][j][0];
					char ConSupFzj0[60];
					sprintf(ConSupFzj0, "ConSupFzj0(z%d,j%d)", z, j);
					double LB = 1, UB = 1;
					IloRange SupF0(env, LB, expr, UB, ConSupFzj0);
					NoOfMasterCons++;
					modelMaster.add(SupF0);
					SupFj0.add(SupF0);
					expr.end();
				}
				else {
					IloExpr expr(env, 0);
					expr = Fzjt[z][j][0];
					char ConSupFzj0[60];
					sprintf(ConSupFzj0, "ConSupFzj0(z%d,j%d)", z, j);
					double LB = 0, UB = 0;
					IloRange SupF0(env, LB, expr, UB, ConSupFzj0);
					NoOfMasterCons++;
					modelMaster.add(SupF0);
					SupFj0.add(SupF0);
					expr.end();
				}
			}

			if (z == 3) {
				if (j == 2) {//------ 3 tank contains 2 type at t=0 ------------
					IloExpr expr(env, 0);
					expr = Fzjt[z][j][0];
					char ConSupFzj0[60];
					sprintf(ConSupFzj0, "ConSupFzj0(z%d,j%d)", z, j);
					double LB = 1, UB = 1;
					IloRange SupF0(env, LB, expr, UB, ConSupFzj0);
					NoOfMasterCons++;
					modelMaster.add(SupF0);
					SupFj0.add(SupF0);
					expr.end();
				}

				else {
					IloExpr expr(env, 0);
					expr = Fzjt[z][j][0];
					char ConSupFzj0[60];
					sprintf(ConSupFzj0, "ConSupFzj0(z%d,j%d)", z, j);
					double LB = 0, UB = 0;
					IloRange SupF0(env, LB, expr, UB, ConSupFzj0);
					NoOfMasterCons++;
					modelMaster.add(SupF0);
					SupFj0.add(SupF0);
					expr.end();
				}

			}



			if (z == 4) {//------ 4 tank is empty at t=0 ------------
				IloExpr expr(env, 0);
				expr = Fzjt[z][j][0];
				char ConSupFzj0[60];
				sprintf(ConSupFzj0, "ConSupFzj0(z%d,j%d)", z, j);
				double LB = 0, UB = 0;
				IloRange SupF0(env, LB, expr, UB, ConSupFzj0);
				NoOfMasterCons++;
				modelMaster.add(SupF0);
				SupFj0.add(SupF0);
				expr.end();
			}

			if (z == 5) {//------ 5 tank is empty at t=0 ------------
				IloExpr expr(env, 0);
				expr = Fzjt[z][j][0];
				char ConSupFzj0[60];
				sprintf(ConSupFzj0, "ConSupFzj0(z%d,j%d)", z, j);
				double LB = 0, UB = 0;
				IloRange SupF0(env, LB, expr, UB, ConSupFzj0);
				NoOfMasterCons++;
				modelMaster.add(SupF0);
				SupFj0.add(SupF0);
				expr.end();
			}

		}
		SupFzj0.add(SupFj0);
	}

	//--------------- No loading taking place at t=0 ------------
	IloRangeMatrix2x2 SupCiz0(env, 0);
	for (i = 0; i < imax; i++) {
		IloRangeArray SupCz0(env, 0);
		for (z = 0; z < zmax; z++) {
			IloExpr expr(env, 0);
			expr = Cizt[i][z][0];
			char ConSupCiz0[60];
			sprintf(ConSupCiz0, "ConSupCiz0(i%d,z%d)", i, z);
			double LB = 0, UB = 0;
			IloRange SupC0(env, LB, expr, UB, ConSupCiz0);
			NoOfMasterCons++;
			modelMaster.add(SupC0);
			SupCz0.add(SupC0);
			expr.end();
		}
		SupCiz0.add(SupCz0);
	}

	//--------------- No unloading taking place at t=0 ------------
	IloRangeMatrix2x2 SupDkz0(env, 0);
	for (k = 0; k < kmax; k++) {
		IloRangeArray SupDz0(env, 0);
		for (z = 0; z < zmax; z++) {
			IloExpr expr(env, 0);
			expr = Dkzt[k][z][0];
			char ConSupDkz0[60];
			sprintf(ConSupDkz0, "ConSupDkz0(k%d,z%d)", k, z);
			double LB = 0, UB = 0;
			IloRange SupD0(env, LB, expr, UB, ConSupDkz0);
			NoOfMasterCons++;
			modelMaster.add(SupD0);
			SupDz0.add(SupD0);
			expr.end();
		}
		SupDkz0.add(SupDz0);
	}

	//-------------------------------Finish of INITIAL VALUES (t=0) ---------------------------------

	//Contrainte de feasabilitι////////////////////////////

	IloRangeMatrix2x2 Con3W1it(env, 0);
	for (i = 0; i < imax; i++) {
		IloRangeArray Con3W1t(env, 0);
		for (t = 0; t < tmax; t++) {
			IloExpr expr(env, 0);
			for (z = 0; z < zmax; z++) {
				expr += Cizt[i][z][t];
			}
			char CT3W1[60];
			sprintf(CT3W1, "CT3W1it(i%d,t%d)", i, t);
			double LB = E_it[i][t] / 100000, UB = IloInfinity;
			IloRange Con3W1(env, LB, expr, UB, CT3W1);
			NoOfMasterCons++;
			modelMaster.add(Con3W1);
			Con3W1t.add(Con3W1);
			expr.end();
		}
		Con3W1it.add(Con3W1t);
	}


	IloRangeMatrix2x2 Con5W2kt(env, 0);
	for (k = 0; k < kmax; k++) {
		IloRangeArray Con5W2t(env, 0);
		for (t = 0; t < tmax; t++) {
			IloExpr expr(env, 0);
			for (z = 0; z < zmax; z++) {
				expr += Dkzt[k][z][t];
			}
			char CT5W2[60];
			sprintf(CT5W2, "CT5W2kt(k%d,t%d)", k, t);
			double LB = S_kt[k][t] / 100000, UB = IloInfinity;
			IloRange Con5W2(env, LB, expr, UB, CT5W2);
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


	//-----------------------------------------------------------------------------
	//------------------------- Slave Primal  Constraintes ------------------------
	//-----------------------------------------------------------------------------
	//------------------------------ Quantite Charge ------------------------------

	for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 SumXjt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloRangeArray SumXt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				for (z = 0; z < zmax; z++) {
					expr += Xizjt[i][z][j][t];
				}
				char Quantite_Charge[60];
				sprintf(Quantite_Charge, "SumXizjt(i%d,j%d,t%d)", i, j, t);
				double LBSumXijt = E_it[i][t] * ae_ijt[i][j][t], UBSumXijt = IloInfinity;
				IloRange SumX(env, LBSumXijt, expr, UBSumXijt, Quantite_Charge);
				NoOfMasterCons++;
				modelMaster.add(SumX);
				SumXt.add(SumX);
				expr.end();
			}

			SumXjt.add(SumXt);
		}

		SumXijt.add(SumXjt);
	}

	for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 DSumXjt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloRangeArray DSumXt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				for (z = 0; z < zmax; z++) {
					expr += -Xizjt[i][z][j][t];
				}
				char DQuantite_Charge[60];
				sprintf(DQuantite_Charge, "DSumXizjt(i%d,j%d,t%d)", i, j, t);
				double DLBSumXijt = -E_it[i][t] * ae_ijt[i][j][t], DUBSumXijt = IloInfinity;
				IloRange DSumX(env, DLBSumXijt, expr, DUBSumXijt, DQuantite_Charge);
				NoOfMasterCons++;
				modelMaster.add(DSumX);
				DSumXt.add(DSumX);
				expr.end();
			}

			DSumXjt.add(DSumXt);
		}

		DSumXijt.add(DSumXjt);
	}

	//-----------------------------------------------------------------------------
	//-------------------------- Quantite Decharge --------------------------------

	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 SumYjt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloRangeArray SumYt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env);
				for (z = 0; z < zmax; z++) {
					expr += Yzkjt[z][k][j][t];
				}
				char Quantite_Decharge[60];
				sprintf(Quantite_Decharge, "SumYzkjt(k%d,j%d,t%d)", k, j, t);
				double LBSumYkjt = S_kt[k][t] * as_kjt[k][j][t], UBSumYkjt = IloInfinity;
				IloRange SumY(env, LBSumYkjt, expr, UBSumYkjt, Quantite_Decharge);
				NoOfMasterCons++;
				modelMaster.add(SumY);
				SumYt.add(SumY);
				expr.end();
			}
			SumYjt.add(SumYt);
		}
		SumYkjt.add(SumYjt);
	}



	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 DSumYjt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloRangeArray DSumYt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env);
				for (z = 0; z < zmax; z++) {
					expr += -Yzkjt[z][k][j][t];
				}
				char DQuantite_Decharge[60];
				sprintf(DQuantite_Decharge, "DSumYzkjt(k%d,j%d,t%d)", k, j, t);
				double DLBSumYkjt = -S_kt[k][t] * as_kjt[k][j][t], DUBSumYkjt = IloInfinity;
				IloRange DSumY(env, DLBSumYkjt, expr, DUBSumYkjt, DQuantite_Decharge);
				NoOfMasterCons++;
				modelMaster.add(DSumY);
				DSumYt.add(DSumY);
				expr.end();
			}
			DSumYjt.add(DSumYt);
		}
		DSumYkjt.add(DSumYjt);
	}



	//-----------------------------------------------------------------------------
	//---------------------------- Equation d'equilibre ---------------------------

	for (z = 0; z < zmax; z++) {
		IloRangeMatrix2x2 CTIjt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloRangeArray CTIt(env, 0);
			for (t = 0; t < tmax; t++) {
				if (t == 0) {
					IloExpr expr(env);
					for (i = 0; i < imax; i++) {
						expr -= Xizjt[i][z][j][t];
					}
					for (k = 0; k < kmax; k++) {
						expr += Yzkjt[z][k][j][t];
					}
					expr += Izjt[z][j][t];
					char Equoition_equilibre[60];
					sprintf(Equoition_equilibre, "CTIzjt(z%d,j%d,t%d)", z, j, t);
					double LBCTIzjt = initial_zj[z][j], UBCTIzjt = IloInfinity;
					IloRange CTI(env, LBCTIzjt, expr, UBCTIzjt, Equoition_equilibre);
					NoOfMasterCons++;
					modelMaster.add(CTI);
					CTIt.add(CTI);
					expr.end();

				}

				else {

					IloExpr expr(env);

					for (i = 0; i < imax; i++) {
						expr -= Xizjt[i][z][j][t];
					}
					for (k = 0; k < kmax; k++) {
						expr += Yzkjt[z][k][j][t];
					}
					expr += Izjt[z][j][t] - Izjt[z][j][t - 1];
					char Equoition_equilibre[60];
					sprintf(Equoition_equilibre, "CTIzjt(z%d,j%d,t%d)", z, j, t);
					double LBCTIzjt = 0, UBCTIzjt = IloInfinity;
					IloRange CTI(env, LBCTIzjt, expr, UBCTIzjt, Equoition_equilibre);
					NoOfMasterCons++;
					modelMaster.add(CTI);
					CTIt.add(CTI);
					expr.end();
				}

			}
			CTIjt.add(CTIt);
		}
		CTIzjt.add(CTIjt);
	}


	for (z = 0; z < zmax; z++) {
		IloRangeMatrix2x2 DCTIjt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloRangeArray DCTIt(env, 0);
			for (t = 0; t < tmax; t++) {
				if (t == 0) {
					IloExpr expr(env);
					for (i = 0; i < imax; i++) {
						expr += Xizjt[i][z][j][t];
					}
					for (k = 0; k < kmax; k++) {
						expr += -Yzkjt[z][k][j][t];
					}
					expr += -Izjt[z][j][t];
					char DEquoition_equilibre[60];
					sprintf(DEquoition_equilibre, "DCTIzjt(z%d,j%d,t%d)", z, j, t);
					double DLBCTIzjt = -initial_zj[z][j], DUBCTIzjt = IloInfinity;
					IloRange DCTI(env, DLBCTIzjt, expr, DUBCTIzjt, DEquoition_equilibre);
					NoOfMasterCons++;
					modelMaster.add(DCTI);
					DCTIt.add(DCTI);
					expr.end();

				}

				else {

					IloExpr expr(env);

					for (i = 0; i < imax; i++) {
						expr += Xizjt[i][z][j][t];
					}
					for (k = 0; k < kmax; k++) {
						expr += -Yzkjt[z][k][j][t];
					}
					expr += -Izjt[z][j][t] + Izjt[z][j][t - 1];
					char DEquoition_equilibre[60];
					sprintf(DEquoition_equilibre, "DCTIzjt(z%d,j%d,t%d)", z, j, t);
					double DLBCTIzjt = 0, DUBCTIzjt = IloInfinity;
					IloRange DCTI(env, DLBCTIzjt, expr, DUBCTIzjt, DEquoition_equilibre);
					NoOfMasterCons++;
					modelMaster.add(DCTI);
					DCTIt.add(DCTI);
					expr.end();
				}

			}
			DCTIjt.add(DCTIt);
		}
		DCTIzjt.add(DCTIjt);
	}

	//-----------------------------------------------------------------------------
	//----------------------------- Capacite de Stockage --------------------------

	for (z = 0; z < zmax; z++) {
		IloRangeArray Sum_It(env, 0);
		for (t = 0; t < tmax; t++) {
			IloExpr expr(env, 0);
			for (j = 0; j < jmax; j++) {
				expr += -Izjt[z][j][t];
			}
			char Capacite_Stockage[60];
			sprintf(Capacite_Stockage, "Sum_Izt(z%d,t%d)", z, t);
			double LBSum_Izt = -1 * capmax, UBSum_Izt = IloInfinity;
			IloRange Sum_I(env, LBSum_Izt, expr, UBSum_Izt, Capacite_Stockage);
			NoOfMasterCons++;
			modelMaster.add(Sum_I);
			Sum_It.add(Sum_I);
			expr.end();
		}
		Sum_Izt.add(Sum_It);
	}

	//-----------------------------------------------------------------------------
	//------------------------------ Contrainte de Fonctionement ------------------
	//-----------------------------------------------------------------------------
	//------------------------------- Chargement CT1 ------------------------------

	for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 CT1Fonctionement_Czt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray CT1Fonctionement_Ct(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				for (j = 0; j < jmax; j++) {
					expr += -Xizjt[i][z][j][t];
				}
				expr += BigM * Cizt[i][z][t];
				char ChargementCT1[60];
				sprintf(ChargementCT1, "CT1Fonctionement_Cizt(i%d,z%d,t%d)", i, z, t);
				double LBCaCT1 = 0, UBCaCT1 = IloInfinity;
				IloRange CT1Fonctionement_C(env, LBCaCT1, expr, UBCaCT1, ChargementCT1);
				NoOfMasterCons++;
				modelMaster.add(CT1Fonctionement_C);
				CT1Fonctionement_Ct.add(CT1Fonctionement_C);
				expr.end();
			}
			CT1Fonctionement_Czt.add(CT1Fonctionement_Ct);
		}
		CT1Fonctionement_Cizt.add(CT1Fonctionement_Czt);
	}
	//--------------------------------------------------------------------------------
	//--------------------------------------------------------------------------------
	//------------------------------- Chargement CT2 ---------------------------------
	//--------------------------------------------------------------------------------

	for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 CT2Fonctionement_Czt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray CT2Fonctionement_Ct(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				for (j = 0; j < jmax; j++) {
					expr += Xizjt[i][z][j][t];
				}
				expr += -Cizt[i][z][t];
				char ChargementCT2[60];
				sprintf(ChargementCT2, "CT2Fonctionement_Cizt(i%d,z%d,t%d)", i, z, t);
				double LBCaCT2 = 0, UBCaCT2 = IloInfinity;
				IloRange CT2Fonctionement_C(env, LBCaCT2, expr, UBCaCT2, ChargementCT2);
				NoOfMasterCons++;
				modelMaster.add(CT2Fonctionement_C);
				CT2Fonctionement_Ct.add(CT2Fonctionement_C);
				expr.end();
			}
			CT2Fonctionement_Czt.add(CT2Fonctionement_Ct);
		}
		CT2Fonctionement_Cizt.add(CT2Fonctionement_Czt);
	}

	//------------------------------- Dechargement CT1 ---------------------------------

	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 CT1Fonctionement_Dzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray CT1Fonctionement_Dt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				for (j = 0; j < jmax; j++) {
					expr += -Yzkjt[z][k][j][t];
				}
				expr += BigM * Dkzt[k][z][t];
				char DechargementCT1[60];
				sprintf(DechargementCT1, "CT1Fonctionement_Dkzt(k%d,z%d,t%d)", k, z, t);
				double LBDeCT1 = 0, UBDeCT1 = IloInfinity;
				IloRange CT1Fonctionement_D(env, LBDeCT1, expr, UBDeCT1, DechargementCT1);
				NoOfMasterCons++;
				modelMaster.add(CT1Fonctionement_D);
				CT1Fonctionement_Dt.add(CT1Fonctionement_D);
				expr.end();
			}
			CT1Fonctionement_Dzt.add(CT1Fonctionement_Dt);
		}
		CT1Fonctionement_Dkzt.add(CT1Fonctionement_Dzt);
	}
	//------------------------------- Dechargement CT2 ---------------------------------

	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 CT2Fonctionement_Dzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray CT2Fonctionement_Dt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				for (j = 0; j < jmax; j++) {
					expr += Yzkjt[z][k][j][t];
				}
				expr += -Dkzt[k][z][t];
				char DechargementCT2[60];
				sprintf(DechargementCT2, "CT2Fonctionement_Dkzt(k%d,z%d,t%d)", k, z, t);
				double LBDeCT2 = 0, UBDeCT2 = IloInfinity;
				IloRange CT2Fonctionement_D(env, LBDeCT2, expr, UBDeCT2, DechargementCT2);
				NoOfMasterCons++;
				modelMaster.add(CT2Fonctionement_D);
				CT2Fonctionement_Dt.add(CT2Fonctionement_D);
				expr.end();
			}
			CT2Fonctionement_Dzt.add(CT2Fonctionement_Dt);
		}
		CT2Fonctionement_Dkzt.add(CT2Fonctionement_Dzt);
	}

	//------------------------------------------------------------------------------
	//--------------------------- Contrainte de melange ----------------------------
	//-------------------------- Contrainte de melange CT1 -------------------------

	for (z = 0; z < zmax; z++) {
		IloRangeMatrix2x2 CT1Meljt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloRangeArray CT1Melt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				expr += -Izjt[z][j][t];
				expr += BigM * Fzjt[z][j][t];
				char CT1Melange[60];
				sprintf(CT1Melange, "CT1Melzjt(z%d,j%d,t%d)", z, j, t);
				double LBCT1Melzjt = 0, UBCT1Melzjt = IloInfinity;
				IloRange CT1Mel(env, LBCT1Melzjt, expr, UBCT1Melzjt, CT1Melange);
				NoOfMasterCons++;
				modelMaster.add(CT1Mel);
				CT1Melt.add(CT1Mel);
				expr.end();
			}
			CT1Meljt.add(CT1Melt);
		}
		CT1Melzjt.add(CT1Meljt);
	}
	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//-------------------------- Contrainte de melange CT2 -------------------------

	for (z = 0; z < zmax; z++) {
		IloRangeMatrix2x2 CT2Meljt(env, 0);
		for (j = 0; j < jmax; j++) {
			IloRangeArray CT2Melt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				expr += Izjt[z][j][t];
				expr += -Fzjt[z][j][t];
				char CT2Melange[60];
				sprintf(CT2Melange, "CT2Melzjt(z%d,j%d,t%d)", z, j, t);
				double LBCT2Melzjt = 0, UBCT2Melzjt = IloInfinity;
				IloRange CT2Mel(env, LBCT2Melzjt, expr, UBCT2Melzjt, CT2Melange);
				NoOfMasterCons++;
				modelMaster.add(CT2Mel);
				CT2Melt.add(CT2Mel);
				expr.end();
			}
			CT2Meljt.add(CT2Melt);
		}
		CT2Melzjt.add(CT2Meljt);
	}

	//------------------------------------------------------------------------------
	//--------------------------- On paye le Setup au debut ------------------------
	//----------------------------------- Chargement -----------------------------

	for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 SC2_Czt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray SC2_Ct(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				expr += -SCizt[i][z][t];
				expr += Cizt[i][z][t];
				char CTSC2_Cizt[60];
				sprintf(CTSC2_Cizt, "SC2_Cizt(i%d,z%d,t%d)", i, z, t);
				double LBSC2_Cizt2 = 0, UBSC2_Cizt2 = IloInfinity;
				IloRange SC2_C(env, LBSC2_Cizt2, expr, UBSC2_Cizt2, CTSC2_Cizt);
				NoOfMasterCons++;
				modelMaster.add(SC2_C);
				SC2_Ct.add(SC2_C);
				expr.end();
			}
			SC2_Czt.add(SC2_Ct);
		}
		SC2_Cizt.add(SC2_Czt);
	}

	//------------------------------------------------------------------------------
	//--------------------------- On paye le Setup au debut ------------------------
	//----------------------------------- Dechargement -----------------------------

	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 SD2_Dzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray SD2_Dt(env, 0);
			for (t = 0; t < tmax; t++) {
				IloExpr expr(env, 0);
				expr += -SDkzt[k][z][t];
				expr += Dkzt[k][z][t];
				char CTSD2_Dkzt[60];
				sprintf(CTSD2_Dkzt, "SD2_Dkzt(k%d,z%d,t%d)", k, z, t);
				double LBSD2_Dkzt2 = 0, UBSD2_Dkzt2 = IloInfinity;
				IloRange SD2_D(env, LBSD2_Dkzt2, expr, UBSD2_Dkzt2, CTSD2_Dkzt);
				NoOfMasterCons++;
				modelMaster.add(SD2_D);
				SD2_Dt.add(SD2_D);
				expr.end();
			}
			SD2_Dzt.add(SD2_Dt);
		}
		SD2_Dkzt.add(SD2_Dzt);
	}


	//--------------------------------------------------------------------------------
	//--------------------------- On paye le Setup au debut ------------------------
	//----------------------------------- Chargement ---------------------------------

	for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 SC_Czt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray SC_Ct(env, 0);
			for (t = 0; t < tmax; t++) {
				if (t == 0) {
					IloExpr expr(env, 0);
					expr += SCizt[i][z][t];
					expr += -Cizt[i][z][t];
					char CTSC_Cizt[60];
					sprintf(CTSC_Cizt, "SC_Cizt(i%d,z%d,t%d)", i, z, t);
					double LBSC_Cizt1 = 0, UBSC_Cizt1 = IloInfinity;
					IloRange SC_C(env, LBSC_Cizt1, expr, UBSC_Cizt1, CTSC_Cizt);
					NoOfMasterCons++;
					modelMaster.add(SC_C);
					SC_Ct.add(SC_C);
					expr.end();
				}

				else {
					IloExpr expr(env, 0);
					expr += SCizt[i][z][t];
					expr += -Cizt[i][z][t] + Cizt[i][z][t - 1];
					char CTSC_Cizt[60];
					sprintf(CTSC_Cizt, "SC_Cizt(i%d,z%d,t%d)", i, z, t);
					double LBSC_Cizt2 = 0, UBSC_Cizt2 = IloInfinity;
					IloRange SC_C(env, LBSC_Cizt2, expr, UBSC_Cizt2, CTSC_Cizt);
					NoOfMasterCons++;
					modelMaster.add(SC_C);
					SC_Ct.add(SC_C);
					expr.end();
				}
			}
			SC_Czt.add(SC_Ct);
		}
		SC_Cizt.add(SC_Czt);
	}
	//------------------------------------------------------------------------------
	//--------------------------- On paye le Setup au debut ------------------------
	//----------------------------------- Dechargement -----------------------------

	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 SD_Dzt(env, 0);
		for (z = 0; z < zmax; z++) {
			IloRangeArray SD_Dt(env, 0);
			for (t = 0; t < tmax; t++) {
				if (t == 0) {
					IloExpr expr(env, 0);
					expr += SDkzt[k][z][t];
					expr += -Dkzt[k][z][t];
					char CTSD_Dkzt[60];
					sprintf(CTSD_Dkzt, "SD_Dkzt(k%d,z%d,t%d)", k, z, t);
					double LBSD_Dkzt1 = 0, UBSD_Dkzt1 = IloInfinity;
					IloRange SD_D(env, LBSD_Dkzt1, expr, UBSD_Dkzt1, CTSD_Dkzt);
					NoOfMasterCons++;
					modelMaster.add(SD_D);
					SD_Dt.add(SD_D);
					expr.end();
				}

				else {
					IloExpr expr(env, 0);
					expr += SDkzt[k][z][t];
					expr += -Dkzt[k][z][t] + Dkzt[k][z][t - 1];
					char CTSD_Dkzt[60];
					sprintf(CTSD_Dkzt, "SD_Dkzt(k%d,z%d,t%d)", k, z, t);
					double LBSD_Dkzt2 = 0, UBSD_Dkzt2 = IloInfinity;
					IloRange SD_D(env, LBSD_Dkzt2, expr, UBSD_Dkzt2, CTSD_Dkzt);
					NoOfMasterCons++;
					modelMaster.add(SD_D);
					SD_Dt.add(SD_D);
					expr.end();
				}
			}
			SD_Dzt.add(SD_Dt);
		}
		SD_Dkzt.add(SD_Dzt);
	}

	//------------------------------------------------------------------------------






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
	for (i = 0; i < imax; i++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				expr1 += SCizt[i][z][t];
			}
		}
	}

	for (k = 0; k < kmax; k++) {
		for (z = 0; z < zmax; z++) {
			for (t = 0; t < tmax; t++) {
				expr1 += SDkzt[k][z][t];
			}
		}
	}


	/*
	for (n=0;n<1;n++){
		expr1+=Zn[n];
	}

	*/
	modelMaster.add(IloMinimize(env, expr1));
	expr1.end();
	IloCplex cplexMaster(env);
	cplexMaster.extract(modelMaster);
	cplexMaster.exportModel("modelMaster1.lp");
	cplexMaster.solve();
	env.out() << "Solution status Master1 = " << cplexMaster.getStatus() << endl;
	env.out() << "Solution value Master1= " << cplexMaster.getObjValue() << endl;
	OptimalOriginalObjFunction = cplexMaster.getObjValue();
	Gap = cplexMaster.getMIPRelativeGap();
	for (t = 0; t < tmax; t++) {
		for (z = 0; z < zmax; z++) {
			for (i = 0; i < imax; i++) {
				OptimalCiztValue[i][z][t] = cplexMaster.getValue(Cizt[i][z][t]);
				OptimalSCiztValue[i][z][t] = cplexMaster.getValue(SCizt[i][z][t]);
			}
			for (k = 0; k < kmax; k++) {
				OptimalDkztValue[k][z][t] = cplexMaster.getValue(Dkzt[k][z][t]);
				OptimalSDkztValue[k][z][t] = cplexMaster.getValue(SDkzt[k][z][t]);
				if (OptimalSDkztValue[k][z][t] != 0) {
					cout << "OptimalSDkztValue[" << k << "][" << z << "][" << t << "]=" << OptimalSDkztValue[k][z][t] << endl;
				}
			}
			for (j = 0; j < jmax; j++) {
				OptimalFzjtValue[z][j][t] = cplexMaster.getValue(Fzjt[z][j][t]);
			}
			for (j = 0; j < jmax; j++) {
				for (i = 0; i < imax; i++) {
					OptimalXizjtValue[i][z][j][t] = cplexMaster.getValue(Xizjt[i][z][j][t]);
				}
				for (k = 0; k < kmax; k++) {
					OptimalYzkjtValue[z][k][j][t] = cplexMaster.getValue(Yzkjt[z][k][j][t]);
				}
				OptimalIzjtValue[z][j][t] = cplexMaster.getValue(Izjt[z][j][t]);
			}
		}
	}






	return 0;
}

int PrintOptimalSolution(char* FilePath_Results_ptr) {
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
	sprintf(filepath, "%s/%s/%s_CPLEX_OptimalSolution.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);


	outfile << FileName_Problem_ptr << std::endl;
	outfile << "TotalSolutionTime= " << duration << " seconds " << std::endl;
	outfile << "OptimalityGap= " << Gap << std::endl;
	
	//if((UpperBoundGlobal-LowerBound)/UpperBoundGlobal>0){
	//	fsOptimalSolution<<"OptimalityGap= "<<(UpperBoundGlobal-LowerBound)/UpperBoundGlobal<< std::endl;
	//}else{
	//	fsOptimalSolution<<"OptimalityGap= 0"<< std::endl;
	//}
	outfile << "OptimalObjFunction= " << OptimalOriginalObjFunction << std::endl;
	//fsOptimalSolution<<"OptimalMasterObjFunction= "<<OptimalMasterObjFunction<< std::endl;
	//fsOptimalSolution<<"OptimalSlaveObjFunction= "<<OptimalSlaveObjFunction<< std::endl;
	outfile << "ModelConstraints= " << NoOfMasterCons << std::endl;
	outfile << "ModelVariables= " << NoOfMasterVariables << std::endl;
	outfile << "----------------------------------" << std::endl;
	if (Gap < epsilon)SolutionStatus = 2;//Optimal
	outfile << "SolutionStatus= " << SolutionStatus << std::endl;
	if (OptimalThetaValue > 0.01) {
		outfile << "OptimalThetaValue= " << OptimalThetaValue << std::endl;
	}
	outfile << "----------------------------------" << std::endl;
	//fsOptimalSolution<<"TotalNumberOfFeasibilityCuts= "<<BDFeasCuts<<std::endl;
	//fsOptimalSolution<<"TotalNumberOfOptimalityCuts= "<<BDOptCuts<<std::endl;
	//fsOptimalSolution<<"----------------------------------"<< std::endl;
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

	/*
		std::ostringstream LowerBound;
		LowerBound << "C:\\Results_CrudeOil\\PureBENDERS\\PureBENDERS - LowerBound.txt";
		std::string FileNameLB = LowerBound.str();
		std::ofstream fsLowerBound;
		fsLowerBound.open(FileNameLB.c_str(),std::ios::out );
		for (i=0;i<LowerBoundArray.size();i++){
			fsLowerBound<<LowerBoundArray.at(i)<< std::endl;
		}
		fsLowerBound.close();

		std::ostringstream UpperBound;
		UpperBound << "C:\\Results_CrudeOil\\PureBENDERS\\PureBENDERS - UpperBound.txt";
		std::string FileNameUB = UpperBound.str();
		std::ofstream fsUpperBound;
		fsUpperBound.open(FileNameUB.c_str(),std::ios::out );
		for (i=0;i<UpperBoundArray.size();i++){
			fsUpperBound<<UpperBoundArray.at(i)<< std::endl;
		}
		fsUpperBound.close();

		std::ostringstream UpperBoundGlobal;
		UpperBoundGlobal << "C:\\Results_CrudeOil\\PureBENDERS\\PureBENDERS - UpperBoundGlobal.txt";
		std::string FileNameUBG = UpperBoundGlobal.str();
		std::ofstream fsUpperBoundGlobal;
		fsUpperBoundGlobal.open(FileNameUBG.c_str(),std::ios::out );
		for (i=0;i<UpperBoundGlobalArray.size();i++){
			fsUpperBoundGlobal<<UpperBoundGlobalArray.at(i)<< std::endl;
		}
		fsUpperBoundGlobal.close();


		std::ostringstream dTransY;
		dTransY << "C:\\Results_CrudeOil\\PureBENDERS\\PureBENDERS - DTrasnposeY.txt";
		std::string FileNameDTY = dTransY.str();
		std::ofstream fsdTransY;
		fsdTransY.open(FileNameDTY.c_str(),std::ios::out );
		for (i=0;i<dTy.size();i++){
			fsdTransY<<dTy.at(i)<< std::endl;
		}
		fsdTransY.close();

		std::ostringstream cTransX;
		cTransX << "C:\\Results_CrudeOil\\PureBENDERS\\PureBENDERS - CTrasnposeX.txt";
		std::string FileNameCTX = cTransX.str();
		std::ofstream fscTransX;
		fscTransX.open(FileNameCTX.c_str(),std::ios::out );
		for (i=0;i<cTx.size();i++){
			fscTransX<<cTx.at(i)<< std::endl;
		}
		fscTransX.close();

		std::ostringstream CurrentTheta;
		CurrentTheta << "C:\\Results_CrudeOil\\PureBENDERS\\PureBENDERS - CurrentTheta.txt";
		std::string FileNameCurrentTheta = CurrentTheta.str();
		std::ofstream fsCurrentTheta;
		fsCurrentTheta.open(FileNameCurrentTheta.c_str(),std::ios::out );
		for (i=0;i<zCurrent.size();i++){
			fsCurrentTheta<<zCurrent.at(i)<< std::endl;
		}
		fsCurrentTheta.close();

		std::ostringstream BestSlaveObj;
		BestSlaveObj << "C:\\Results_CrudeOil\\PureBENDERS\\PureBENDERS - BestSlaveObjSoFar.txt";
		std::string FileNameBSO = BestSlaveObj.str();
		std::ofstream fsBestSlaveObj;
		fsBestSlaveObj.open(FileNameBSO.c_str(),std::ios::out );
		for (i=0;i<BestSlaveObjSoFar.size();i++){
			fsBestSlaveObj<<BestSlaveObjSoFar.at(i)<< std::endl;
		}
		fsBestSlaveObj.close();


		std::ostringstream TimePath;
		TimePath << "C:\\Results_CrudeOil\\PureBENDERS\\PureBENDERS - Time.txt";
		std::string FileNameTime = TimePath.str();
		std::ofstream fsTime;
		fsTime.open(FileNameTime.c_str(),std::ios::out );
		for (i=0;i<Time.size();i++){
			fsTime<<Time.at(i)<< std::endl;
		}
		fsTime.close();



		std::ostringstream SlackVals;
		SlackVals << "C:\\Results_CrudeOil\\PureBENDERS\\PureBENDERS - SlackValues.txt";
		std::string FileNameSlack = SlackVals.str();
		std::ofstream fsSlack;
		fsSlack.open(FileNameSlack.c_str(),std::ios::out );
		i=0;
		j=0;
		k=0;
		while (j<BDFeasCuts+BDOptCuts){
			z=0;
			k+=NoOfCutsInEachIteration.at(j);
			while (i<SlackValuesOfBendersCuts.size()&&z<k){
				fsSlack<<SlackValuesOfBendersCuts.at(i)<< "\t";
				z++;
				i++;
			}
			fsSlack<< std::endl;
			j++;
		}
		fsSlack.close();
	*/
	return 0;
}

int main(int argc, char **argv)
{
	int  stop, status;

	status = InsertDataSet(FilePath_DataSet);
	if (status != 0) {
		Found_Error("InsertDataSet");
		return -1;
	}
	status = InsertDataSetIndices(FilePath_DataSet);
	if (status != 0) {
		Found_Error("InsertDataSetIndices");
		return -1;
	}
	for (int i_Problem = 0; i_Problem < TotalNoOfProblems; i_Problem++) {
		strcpy(FileName_Problem, ProblemNames[i_Problem].c_str());
		imax = imaxset[i_Problem];
		zmax = zmaxset[i_Problem];
		kmax = kmaxset[i_Problem];
		jmax = jmaxset[i_Problem];
		tmax = tmaxset[i_Problem];
		cout << "-------------------" << endl;
		cout << "Solving DataSet: " << FileName_Problem << endl;
		cout << "-------------------" << endl;

		//--------Declare the environment of CPLEX----------------
		IloEnv env;
		try {
			//--------Construct models----------------
			IloModel modelSlave1(env);
			IloModel modelMaster(env);

			//------Declare Decision Variables----------
			IloNumVarMatrix3x3 Cizt(env, 0);
			IloNumVarMatrix3x3 Dkzt(env, 0);
			IloNumVarMatrix3x3 Fzjt(env, 0);
			IloNumVarArray Zn(env, 0);
			IloNumVarMatrix4x4 Xizjt(env, 0);
			IloNumVarMatrix4x4 Yzkjt(env, 0);
			IloNumVarMatrix3x3 Izjt(env, 0);
			IloNumVarMatrix3x3 SCizt(env, 0);
			IloNumVarMatrix3x3 SDkzt(env, 0);

			//--------Declare Slave constraints-------------
			IloRangeMatrix3x3 SumXijt(env, 0);
			IloRangeMatrix3x3 DSumXijt(env, 0);
			IloRangeMatrix3x3 SumYkjt(env, 0);
			IloRangeMatrix3x3 DSumYkjt(env, 0);
			IloRangeMatrix3x3 CTIzjt(env, 0);
			IloRangeMatrix3x3 DCTIzjt(env, 0);
			IloRangeMatrix2x2 Sum_Izt(env, 0);
			IloRangeMatrix3x3 CT1Fonctionement_Cizt(env, 0);
			IloRangeMatrix3x3 CT2Fonctionement_Cizt(env, 0);
			IloRangeMatrix3x3 CT1Fonctionement_Dkzt(env, 0);
			IloRangeMatrix3x3 CT2Fonctionement_Dkzt(env, 0);
			IloRangeMatrix3x3 CT1Melzjt(env, 0);
			IloRangeMatrix3x3 CT2Melzjt(env, 0);
			IloRangeMatrix3x3 SC2_Cizt(env, 0);
			IloRangeMatrix3x3 SD2_Dkzt(env, 0);
			IloRangeMatrix3x3 SC_Cizt(env, 0);
			IloRangeMatrix3x3 SD_Dkzt(env, 0);

			//--------Declare Array of Benders Cuts Added in Master Problem-------------
			IloRangeArray BendersCuts(env, 0);

			//----------What does IloNum mean?---------------

			IloNum valsDualRangeSumXijt;
			IloNum valsDualRangeSumYkjt;
			IloNum valsDualRangeCTIzjt;
			IloNum valsDualRangeSum_Izt;
			IloNum valsDualRangeCT1Fonctionement_Cizt;
			IloNum valsDualRangeCT2Fonctionement_Cizt;
			IloNum valsDualRangeCT1Fonctionement_Dkzt;
			IloNum valsDualRangeCT2Fonctionement_Dkzt;

			IloNum valsDualRangeCT1Melzjt;
			IloNum valsDualRangeCT2Melzjt;
			IloNum valsDualRangeSC2_Cizt;
			IloNum valsDualRangeSD2_Dkzt;
			IloNum valsDualRangeSC_Cizt;
			IloNum valsDualRangeSD_Dkzt;

			IloNumArray FeasvalsDualRangeSumXijt(env, 0);
			IloNumArray SlackValues(env, 0);




			status = load_data(FilePath_Data);
			if (status != 0) {
				Found_Error("load_data");
				return -1;
			}
			start = clock();
			status = do_master(env, modelMaster, Cizt, Dkzt, Fzjt, Zn, Xizjt, Yzkjt, Izjt, SCizt, SDkzt, SumXijt, DSumXijt, SumYkjt, DSumYkjt, CTIzjt, DCTIzjt, Sum_Izt, CT1Fonctionement_Cizt, CT2Fonctionement_Cizt, CT1Fonctionement_Dkzt, CT2Fonctionement_Dkzt, CT1Melzjt, CT2Melzjt, SC2_Cizt, SD2_Dkzt, SC_Cizt, SD_Dkzt);
			if (status != 0) {
				Found_Error("do_master");
				return -1;
			}
			stop = clock();
			duration = (long double)(stop - start) / CLOCKS_PER_SEC;

			status = PrintOptimalSolution(FilePath_Results);
			if (status != 0) {
				Found_Error("PrintOptimalSolution");
				return -1;
			}
		}
		catch (IloException& e) {
			cout << "Error : " << e << endl;
		}
		env.end();


		printf("Code terminated successfully \n");
		printf("Execution time = %Lf seconds\n", duration);
	}
	return 0;

} //End main




