#!/usr/bin/env python3
"""
Longevity Evidence Scout v1.5
Automated discovery of healthspan and blood biomarker research from PubMed

Based on ToxEcology Evidence Scout v2.2 architecture
Adapted for longevity science and blood biomarkers

v1.5 CHANGES:
- NEW: Abstract-level inpatient/acute-care exclusion check (before Claude API call)
- NEW: population_type extracted by Claude; inpatient studies are skipped entirely
- NEW: Expanded TOP_JOURNALS with longevity/preventive medicine journals
- REMOVED: "annals of internal medicine" from TOP_JOURNALS (too inpatient-heavy)
- NEW: inpatient_excluded stat counter for visibility into filtered studies

v1.4 CHANGES:
- NEW: domain_keywords loaded from config.yaml with tight, non-overlapping sets
- NEW: Title weighting (3x default) for domain detection
- NEW: Negative keyword exclusions to prevent misclassification
- NEW: Direct DOM_ convention (no intermediate mapping)
- FIXED: Sex hormones no longer classified as DOM_THYROID
- FIXED: RDW studies correctly go to DOM_HEMATOLOGY

v1.3 CHANGES:
- Loosened PubMed filter (removed redundant longevity/aging AND clause)
- Added priority keyword system for domain detection
- Expanded Blood_Counts keywords for better RDW/NLR detection

v1.2 CHANGES:
- Added auto-linking to Health_Conditions and Symptom_Clusters
- Domain → Condition mapping for proper linking
- Caching system for related tables
"""

import os
import sys
import json
import time
import yaml
import requests
import xml.etree.ElementTree as ET
from datetime import datetime
from anthropic import Anthropic

# ============================================================================
# DOMAIN → CONDITION MAPPING (for auto-linking)
# Maps toxin_domain values to Health_Conditions condition_id
# ============================================================================

DOMAIN_TO_CONDITION = {
    "DOM_INFLAMMATION": "COND_005",    # Chronic Inflammation
    "DOM_LIPID": "COND_010",           # Dyslipidemia
    "DOM_HEMATOLOGY": "COND_006",      # Immune Suppression (blood markers)
    "DOM_METABOLIC": "COND_003",       # Metabolic Syndrome
    "DOM_HORMONE": "COND_002",         # Hormonal Imbalance
    "DOM_THYROID": "COND_001",         # Thyroid Dysfunction
    "DOM_KIDNEY": "COND_020",          # Kidney Dysfunction
    "DOM_LIVER": "COND_013",           # Liver Dysfunction
    "DOM_NUTRIENT": "COND_012",        # Detoxification Impairment (nutrient cofactors)
    "DOM_AGING": "COND_017",           # Mitochondrial Dysfunction (aging/longevity)
    "DOM_OXIDATIVE": "COND_005",       # Maps to Chronic Inflammation
    "DOM_METHYLATION": "COND_012",     # Maps to Detoxification Impairment
}

# ============================================================================
# CONFIGURATION
# ============================================================================

ANTHROPIC_KEY = os.environ.get("ANTHROPIC_KEY")
AIRTABLE_API_KEY = os.environ.get("AIRTABLE_API_KEY")

AIRTABLE_BASE_ID = os.environ.get("AIRTABLE_CLINICAL_BASE_ID", "app42HAczcSBeZOxD")
AIRTABLE_TABLE_NAME = "Clinical_Evidence"

HEALTH_CONDITIONS_TABLE = "Health_Conditions"
SYMPTOM_CLUSTERS_TABLE = "Symptom_Clusters"

# High-impact journals for longevity/aging/preventive health research
# v1.5: Removed "annals of internal medicine" (inpatient-heavy). Added
# longevity, preventive medicine, and nutrition-focused journals.
TOP_JOURNALS = [
    # Core longevity / aging science
    "nature aging", "aging cell", "geroscience", "aging",
    "experimental gerontology", "frontiers in aging",
    "journals of gerontology", "age and ageing",
    "journal of gerontology", "lancet healthy longevity",
    # High-impact general / clinical
    "nature medicine", "nature", "science", "cell",
    "cell metabolism", "nejm", "lancet", "jama", "bmj",
    "plos medicine", "plos one", "scientific reports",
    # Cardiovascular / metabolic
    "circulation", "diabetes care", "journal of clinical endocrinology",
    "european heart journal",
    # Preventive medicine & nutrition
    "preventive medicine", "american journal of preventive medicine",
    "nutrients", "journal of nutritional biochemistry",
    "american journal of clinical nutrition",
    "journal of the academy of nutrition and dietetics",
    # Integrative / functional medicine adjacent
    "journal of clinical medicine", "biomedicines",
    "frontiers in nutrition", "frontiers in physiology"
]

# =============================================================================
# VALID EVIDENCE TYPES (must match Airtable single select options)
# =============================================================================

VALID_EVIDENCE_TYPES = [
    "Meta-analysis", "Systematic Review", "RCT", "Prospective Cohort",
    "Cohort", "Case-control", "Cross-sectional", "NHANES", "Biomonitoring",
    "Case Series", "In Vitro", "Animal", "Mechanistic", "Other"
]

def sanitize_evidence_type(evidence_type):
    """Sanitize evidence_type to match valid Airtable single select options."""
    if not evidence_type:
        return "Other"
    
    et = str(evidence_type).strip().strip('"').strip("'")
    et_lower = et.lower()
    
    for valid in VALID_EVIDENCE_TYPES:
        if et_lower == valid.lower():
            return valid
    
    mapping = {
        "meta analysis": "Meta-analysis",
        "systematic review and meta-analysis": "Meta-analysis",
        "systematic review": "Systematic Review",
        "review": "Systematic Review",
        "randomized controlled trial": "RCT",
        "randomised controlled trial": "RCT",
        "randomized clinical trial": "RCT",
        "clinical trial": "RCT",
        "prospective cohort": "Prospective Cohort",
        "prospective study": "Prospective Cohort",
        "prospective": "Prospective Cohort",
        "longitudinal": "Prospective Cohort",
        "cohort study": "Cohort",
        "retrospective cohort": "Cohort",
        "retrospective": "Cohort",
        "case control": "Case-control",
        "case-control study": "Case-control",
        "cross sectional": "Cross-sectional",
        "cross-sectional study": "Cross-sectional",
        "population-based": "Cross-sectional",
        "observational": "Cross-sectional",
        "nhanes analysis": "NHANES",
        "nhanes study": "NHANES",
        "biomonitoring study": "Biomonitoring",
        "case series": "Case Series",
        "case report": "Case Series",
        "in vitro": "In Vitro",
        "in-vitro": "In Vitro",
        "animal study": "Animal",
        "animal model": "Animal",
        "in vivo": "Animal",
        "mechanistic study": "Mechanistic",
        "unknown": "Other",
        "not reported": "Other",
        "n/a": "Other",
        "": "Other",
    }
    
    if et_lower in mapping:
        return mapping[et_lower]
    
    if "meta" in et_lower and "analy" in et_lower:
        return "Meta-analysis"
    if "systematic" in et_lower:
        return "Systematic Review"
    if "random" in et_lower or "rct" in et_lower:
        return "RCT"
    if "prospective" in et_lower or "longitudinal" in et_lower:
        return "Prospective Cohort"
    if "cohort" in et_lower:
        return "Cohort"
    if "case-control" in et_lower or "case control" in et_lower:
        return "Case-control"
    if "cross" in et_lower and "section" in et_lower:
        return "Cross-sectional"
    if "nhanes" in et_lower:
        return "NHANES"
    if "biomonitor" in et_lower:
        return "Biomonitoring"
    if "vitro" in et_lower:
        return "In Vitro"
    if "animal" in et_lower or "mouse" in et_lower or "rat" in et_lower:
        return "Animal"
    
    return "Other"


# Statistics tracking
stats = {
    "total_searched": 0,
    "abstracts_fetched": 0,
    "duplicates_skipped": 0,
    "inpatient_excluded": 0,
    "below_threshold": 0,
    "population_type_excluded": 0,
    "added_to_airtable": 0,
    "errors": 0
}

# ============================================================================
# INPATIENT / ACUTE-CARE EXCLUSION  (v1.5)
# These phrases in the title or abstract signal hospital/inpatient populations
# that are NOT relevant to wellness biomarker and healthspan research.
# Checked BEFORE calling Claude to save API costs.
# ============================================================================

INPATIENT_EXCLUSION_PHRASES = [
    "hospitalized patients",
    "hospitalised patients",
    "hospitalized adults",
    "hospitalised adults",
    "hospitalized older",
    "hospitalised older",
    "hospital inpatients",
    "inpatient",
    "intensive care unit",
    "icu patients",
    "icu admission",
    "critically ill",
    "critical illness",
    "acute care",
    "acute illness",
    "mechanically ventilated",
    "mechanical ventilation",
    "acute kidney injury",
    "acute liver failure",
    "acute decompensation",
    "acute respiratory failure",
    "acute respiratory distress",
    "post-operative",
    "postoperative",
    "perioperative",
    "emergency department",
    "emergency admission",
    "hospital admission",
    "hospital-acquired",
    "hospital acquired",
    "sepsis patients",
    "septic shock",
    "hemodialysis patients",
    "dialysis patients",
    "end-stage renal disease",
    "end stage renal",
    "liver transplant",
    "organ transplant",
    "blood transfusion",
    "chemotherapy patients",
    "oncology patients",
    "cancer patients",
    "critically injured",
    "trauma patients",
    "surgical patients",
    "cardiothoracic surgery",
    "cardiac surgery patients",
]


def is_inpatient_study(title: str, abstract: str) -> tuple[bool, str]:
    """
    Check whether a study's title+abstract signals an inpatient/acute-care
    population.  Returns (True, matched_phrase) if exclusion applies,
    (False, '') otherwise.
    """
    combined = f"{title} {abstract}".lower()
    for phrase in INPATIENT_EXCLUSION_PHRASES:
        if phrase in combined:
            return True, phrase
    return False, ""

# ============================================================================
# AIRTABLE CACHING FUNCTIONS
# ============================================================================

_existing_titles_cache = None
_health_conditions_cache = None
_symptom_clusters_cache = None

def get_airtable_headers():
    return {
        "Authorization": f"Bearer {AIRTABLE_API_KEY}",
        "Content-Type": "application/json"
    }

def get_existing_titles():
    """Fetch all existing study titles for duplicate detection"""
    global _existing_titles_cache
    if _existing_titles_cache is not None:
        return _existing_titles_cache
    
    url = f"https://api.airtable.com/v0/{AIRTABLE_BASE_ID}/{AIRTABLE_TABLE_NAME}"
    headers = get_airtable_headers()
    
    titles = set()
    offset = None
    
    try:
        while True:
            params = {"fields[]": "study_title", "pageSize": 100}
            if offset:
                params["offset"] = offset
            
            response = requests.get(url, headers=headers, params=params, timeout=30)
            
            if response.status_code == 404:
                print(f"📋 Table {AIRTABLE_TABLE_NAME} not found - will create records fresh")
                _existing_titles_cache = set()
                return _existing_titles_cache
            
            response.raise_for_status()
            data = response.json()
            
            for record in data.get("records", []):
                title = record.get("fields", {}).get("study_title", "")
                if title:
                    titles.add(title.lower().strip())
            
            offset = data.get("offset")
            if not offset:
                break
        
        print(f"📋 Loaded {len(titles)} existing study titles for dedup")
        _existing_titles_cache = titles
        return _existing_titles_cache
    
    except requests.exceptions.RequestException as e:
        print(f"⚠️ Warning loading existing titles: {e}")
        _existing_titles_cache = set()
        return _existing_titles_cache


def load_health_conditions():
    """Load Health_Conditions table into cache for auto-linking"""
    global _health_conditions_cache
    if _health_conditions_cache is not None:
        return _health_conditions_cache
    
    print("📋 Loading Health_Conditions table...")
    url = f"https://api.airtable.com/v0/{AIRTABLE_BASE_ID}/{HEALTH_CONDITIONS_TABLE}"
    headers = get_airtable_headers()
    records = []
    offset = None
    
    try:
        while True:
            params = {"pageSize": 100}
            if offset:
                params["offset"] = offset
            
            response = requests.get(url, headers=headers, params=params, timeout=30)
            if response.status_code != 200:
                print(f"   ⚠️ Error loading Health_Conditions: {response.status_code}")
                _health_conditions_cache = {}
                return _health_conditions_cache
            
            data = response.json()
            records.extend(data.get("records", []))
            
            offset = data.get("offset")
            if not offset:
                break
        
        _health_conditions_cache = {}
        for rec in records:
            cond_id = rec["fields"].get("condition_id")
            if cond_id:
                _health_conditions_cache[cond_id] = rec["id"]
        
        print(f"   ✅ Loaded {len(_health_conditions_cache)} health conditions")
    except Exception as e:
        print(f"   ⚠️ Exception loading Health_Conditions: {e}")
        _health_conditions_cache = {}
    
    return _health_conditions_cache


def load_symptom_clusters():
    """Load Symptom_Clusters table into cache for auto-linking"""
    global _symptom_clusters_cache
    if _symptom_clusters_cache is not None:
        return _symptom_clusters_cache
    
    print("📋 Loading Symptom_Clusters table...")
    url = f"https://api.airtable.com/v0/{AIRTABLE_BASE_ID}/{SYMPTOM_CLUSTERS_TABLE}"
    headers = get_airtable_headers()
    records = []
    offset = None
    
    try:
        while True:
            params = {"pageSize": 100}
            if offset:
                params["offset"] = offset
            
            response = requests.get(url, headers=headers, params=params, timeout=30)
            if response.status_code != 200:
                print(f"   ⚠️ Error loading Symptom_Clusters: {response.status_code}")
                _symptom_clusters_cache = {}
                return _symptom_clusters_cache
            
            data = response.json()
            records.extend(data.get("records", []))
            
            offset = data.get("offset")
            if not offset:
                break
        
        _symptom_clusters_cache = {}
        for rec in records:
            cond_id = rec["fields"].get("primary_condition_id")
            if cond_id:
                if cond_id not in _symptom_clusters_cache:
                    _symptom_clusters_cache[cond_id] = []
                _symptom_clusters_cache[cond_id].append(rec["id"])
        
        print(f"   ✅ Loaded {len(records)} symptom clusters")
    except Exception as e:
        print(f"   ⚠️ Exception loading Symptom_Clusters: {e}")
        _symptom_clusters_cache = {}
    
    return _symptom_clusters_cache


# ============================================================================
# LINKING FUNCTIONS
# ============================================================================

def find_health_condition_link(condition_id):
    if not condition_id:
        return None
    cache = load_health_conditions()
    return cache.get(condition_id)


def find_symptom_cluster_links(condition_id):
    if not condition_id:
        return []
    cache = load_symptom_clusters()
    return cache.get(condition_id, [])


def get_condition_from_domain(domain):
    return DOMAIN_TO_CONDITION.get(domain)


# ============================================================================
# PUBMED API FUNCTIONS
# ============================================================================

def search_pubmed(query, max_results=30, date_after="2024-01-01"):
    """Search PubMed and return list of PMIDs"""
    base_url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi"
    
    full_query = f"({query}) AND human[MeSH Terms]"
    
    params = {
        "db": "pubmed",
        "term": full_query,
        "retmax": max_results,
        "retmode": "json",
        "sort": "date",
        "mindate": date_after.replace("-", "/"),
        "maxdate": datetime.now().strftime("%Y/%m/%d"),
        "datetype": "pdat"
    }
    
    try:
        response = requests.get(base_url, params=params, timeout=30)
        response.raise_for_status()
        data = response.json()
        pmids = data.get("esearchresult", {}).get("idlist", [])
        stats["total_searched"] += len(pmids)
        return pmids
    except requests.exceptions.RequestException as e:
        print(f"⚠️ PubMed search error: {e}")
        stats["errors"] += 1
        return []


def fetch_pubmed_abstract(pmid):
    """Fetch article metadata and abstract from PubMed"""
    base_url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi"
    params = {
        "db": "pubmed",
        "id": pmid,
        "retmode": "xml"
    }
    
    try:
        response = requests.get(base_url, params=params, timeout=30)
        response.raise_for_status()
        
        try:
            content = response.content.decode('utf-8', errors='replace')
        except:
            content = response.text
        
        content = ''.join(char for char in content if char.isprintable() or char in '\n\r\t')
        
        root = ET.fromstring(content.encode('utf-8'))
        article = root.find(".//PubmedArticle")
        
        if article is None:
            return None
        
        title = article.findtext(".//ArticleTitle", "")
        
        abstract_parts = []
        for abstract_elem in article.findall(".//AbstractText"):
            if abstract_elem.text:
                label = abstract_elem.get("Label", "")
                if label:
                    abstract_parts.append(f"{label}: {abstract_elem.text}")
                else:
                    abstract_parts.append(abstract_elem.text)
        abstract = " ".join(abstract_parts) if abstract_parts else ""
        
        journal = article.findtext(".//Journal/Title", "")
        year = article.findtext(".//PubDate/Year", "")
        
        if not year:
            medline_date = article.findtext(".//PubDate/MedlineDate", "")
            if medline_date:
                year = medline_date[:4]
        
        if not year:
            year = str(datetime.now().year)
        
        authors = []
        for author in article.findall(".//Author"):
            lastname = author.findtext("LastName", "")
            initials = author.findtext("Initials", "")
            if lastname:
                authors.append(f"{lastname} {initials}")
        
        stats["abstracts_fetched"] += 1
        
        return {
            "pmid": pmid,
            "title": title,
            "abstract": abstract,
            "journal": journal,
            "year": year,
            "authors": ", ".join(authors[:5]) + (" et al." if len(authors) > 5 else ""),
            "url": f"https://pubmed.ncbi.nlm.nih.gov/{pmid}/"
        }
    
    except ET.ParseError as e:
        print(f"   ⚠️ XML parse error for {pmid}: {e}")
        stats["errors"] += 1
        return None
    except Exception as e:
        print(f"⚠️ Error fetching PMID {pmid}: {e}")
        stats["errors"] += 1
        return None


# ============================================================================
# DOMAIN DETECTION v1.4 - Title Weighting + Negative Keywords
# ============================================================================

# Global cache for domain keywords loaded from config
_domain_keywords_cache = None

def load_domain_keywords(config):
    """Load domain_keywords from config.yaml into global cache"""
    global _domain_keywords_cache
    if _domain_keywords_cache is not None:
        return _domain_keywords_cache
    
    _domain_keywords_cache = config.get("domain_keywords", {})
    if _domain_keywords_cache:
        print(f"📋 Loaded domain_keywords for {len(_domain_keywords_cache)} domains")
    else:
        print("⚠️ No domain_keywords in config, using fallback detection")
    
    return _domain_keywords_cache


def detect_domain(title, abstract, query, config):
    """
    Auto-detect longevity domain using:
    1. Title weighting (keywords in title count 3x by default)
    2. Negative keyword exclusions
    3. Primary keyword matching
    
    v1.4: Now uses domain_keywords from config.yaml
    """
    domain_keywords = load_domain_keywords(config)
    
    if not domain_keywords:
        # Fallback to simple keyword detection if no config
        return _detect_domain_fallback(title, abstract, query)
    
    title_lower = title.lower()
    abstract_lower = abstract.lower()
    query_lower = query.lower()
    
    # Combine all text for searching
    full_text = f"{title_lower} {abstract_lower} {query_lower}"
    
    domain_scores = {}
    
    for domain, keywords_config in domain_keywords.items():
        primary = keywords_config.get("primary", [])
        negative = keywords_config.get("negative", [])
        title_weight = keywords_config.get("title_weight", 3)
        
        # Check negative keywords first - if any match, skip this domain
        has_negative = False
        for neg_kw in negative:
            if neg_kw.lower() in full_text:
                has_negative = True
                break
        
        if has_negative:
            continue
        
        # Score based on primary keywords
        score = 0
        for kw in primary:
            kw_lower = kw.lower()
            
            # Title matches get weighted score
            if kw_lower in title_lower:
                score += title_weight
            
            # Abstract/query matches get normal score
            if kw_lower in abstract_lower or kw_lower in query_lower:
                score += 1
        
        if score > 0:
            domain_scores[domain] = score
    
    if domain_scores:
        best_domain = max(domain_scores, key=domain_scores.get)
        best_score = domain_scores[best_domain]
        
        # Debug output for domain detection
        print(f"   🎯 Domain scores: {dict(sorted(domain_scores.items(), key=lambda x: -x[1])[:3])}")
        print(f"   ✓ Selected: {best_domain} (score: {best_score})")
        
        return best_domain
    
    return "DOM_AGING"  # Default fallback


def _detect_domain_fallback(title, abstract, query):
    """Fallback domain detection if no config keywords available"""
    text = f"{title} {abstract} {query}".lower()
    
    # Priority keywords (most specific)
    priority = {
        "rdw": "DOM_HEMATOLOGY",
        "red cell distribution width": "DOM_HEMATOLOGY",
        "anisocytosis": "DOM_HEMATOLOGY",
        "testosterone": "DOM_HORMONE",
        "estrogen": "DOM_HORMONE",
        "shbg": "DOM_HORMONE",
        "tsh": "DOM_THYROID",
        "thyroid": "DOM_THYROID",
        "homocysteine": "DOM_METHYLATION",
        "egfr": "DOM_KIDNEY",
        "creatinine": "DOM_KIDNEY",
        "alt": "DOM_LIVER",
        "ggt": "DOM_LIVER",
        "ldl": "DOM_LIPID",
        "cholesterol": "DOM_LIPID",
        "crp": "DOM_INFLAMMATION",
        "interleukin": "DOM_INFLAMMATION",
        "glucose": "DOM_METABOLIC",
        "insulin": "DOM_METABOLIC",
        "hba1c": "DOM_METABOLIC",
        "telomere": "DOM_AGING",
        "epigenetic clock": "DOM_AGING",
        "biological age": "DOM_AGING",
        "vitamin d": "DOM_NUTRIENT",
        "vitamin b12": "DOM_NUTRIENT",
        "ferritin": "DOM_NUTRIENT",
        "oxidative stress": "DOM_OXIDATIVE",
        "glutathione": "DOM_OXIDATIVE",
    }
    
    for kw, domain in priority.items():
        if kw in text:
            return domain
    
    return "DOM_AGING"


# ============================================================================
# EVIDENCE SCORING
# ============================================================================

def calculate_stars(evidence_type, sample_size, journal, effect_size_reported):
    """Calculate evidence strength score (1-5 stars)"""
    score = 0
    
    evidence_type_lower = evidence_type.lower() if evidence_type else ""
    
    if "meta-analysis" in evidence_type_lower or "systematic review" in evidence_type_lower:
        score += 2.5
    elif "randomized" in evidence_type_lower or "rct" in evidence_type_lower:
        score += 2.5
    elif "prospective cohort" in evidence_type_lower or "longitudinal" in evidence_type_lower:
        score += 2.0
    elif "cohort" in evidence_type_lower or "case-control" in evidence_type_lower:
        score += 1.5
    elif "cross-sectional" in evidence_type_lower or "nhanes" in evidence_type_lower or "population" in evidence_type_lower:
        score += 1.0
    elif "case series" in evidence_type_lower or "case report" in evidence_type_lower:
        score += 0.5
    else:
        score += 0.5
    
    if sample_size:
        try:
            size_str = str(sample_size).replace(",", "").replace(" ", "")
            n = int(''.join(filter(str.isdigit, size_str.split()[0] if size_str.split() else size_str)))
            
            if n >= 10000:
                score += 1.5
            elif n >= 1000:
                score += 1.0
            elif n >= 500:
                score += 0.75
            elif n >= 100:
                score += 0.5
            elif n >= 50:
                score += 0.25
        except (ValueError, IndexError):
            pass
    
    journal_lower = journal.lower() if journal else ""
    if any(top in journal_lower for top in TOP_JOURNALS):
        score += 1.0
    else:
        score += 0.5
    
    if effect_size_reported and effect_size_reported.lower() not in ["not reported", "n/a", "none", ""]:
        score += 0.5
        if any(x in effect_size_reported.lower() for x in ["per", "dose", "quartile", "tertile", "trend"]):
            score += 0.25
    
    return min(max(round(score), 1), 5)
    

def format_stars(num):
    return f"{num} " + "⭐️" * num


# ============================================================================
# CLAUDE AI EXTRACTION
# ============================================================================

def ask_claude(article, domain):
    """Use Claude to extract structured metadata from abstract"""
    client = Anthropic(api_key=ANTHROPIC_KEY)

    prompt = f"""Analyze this longevity/healthspan research article and extract structured information.

TITLE: {article['title']}

ABSTRACT: {article['abstract']}

JOURNAL: {article['journal']}

DETECTED DOMAIN: {domain}

Extract the following in JSON format:
{{
    "evidence_type": "Study design (e.g., 'Meta-analysis', 'RCT', 'Prospective cohort', 'Cross-sectional', 'NHANES')",
    "sample_size": "Number of participants or 'Not reported'",
    "biomarkers_studied": ["list", "of", "biomarkers"],
    "key_findings": "2-3 sentence summary of main findings relevant to longevity/healthspan",
    "effect_size": "Quantified effect (HR, OR, correlation, β, etc.) or 'Not reported'",
    "clinical_relevance": "Practical implications for healthspan optimization",
    "limitations": "Key study limitations",
    "population_type": "Classify the study population as exactly one of: 'community/outpatient' (community-dwelling adults, general population, outpatient cohorts, population-based registries, prevention trials), 'inpatient' (hospitalized patients, ICU, acute care, surgical, critically ill, dialysis), 'mixed' (includes both community and hospital-based populations), or 'not specified' (population setting cannot be determined from abstract)"
}}

Return ONLY valid JSON, no markdown formatting."""

    try:
        response = client.messages.create(
            model=os.environ.get('ANTHROPIC_MODEL', 'claude-sonnet-4-6'),
            max_tokens=1500,
            messages=[{"role": "user", "content": prompt}]
        )
        
        text = response.content[0].text.strip()
        
        if text.startswith("```"):
            text = text.split("\n", 1)[1]
        if text.endswith("```"):
            text = text.rsplit("\n", 1)[0]
        text = text.replace("```json", "").replace("```", "").strip()
        
        return json.loads(text)
    
    except json.JSONDecodeError as e:
        print(f"⚠️ JSON parse error: {e}")
        stats["errors"] += 1
        return None
    except Exception as e:
        print(f"⚠️ Claude API error: {e}")
        stats["errors"] += 1
        return None


# ============================================================================
# AIRTABLE UPLOAD WITH AUTO-LINKING
# ============================================================================

def get_next_evidence_id():
    now = datetime.now()
    return f"LONG_{now.strftime('%m%d%H%M%S')}{stats['added_to_airtable']:03d}"


def add_to_airtable(article, extracted, stars, domain):
    """Upload study to Airtable Clinical_Evidence table with auto-linking"""
    url = f"https://api.airtable.com/v0/{AIRTABLE_BASE_ID}/{AIRTABLE_TABLE_NAME}"
    headers = get_airtable_headers()
    
    # v1.4: domain is already in DOM_ format
    mapped_domain = domain
    
    condition_id = get_condition_from_domain(mapped_domain)
    
    biomarkers = extracted.get("biomarkers_studied", [])
    if isinstance(biomarkers, list):
        biomarkers_str = ", ".join(str(b) for b in biomarkers)
    else:
        biomarkers_str = str(biomarkers) if biomarkers else ""
    
    record = {
        "fields": {
            "evidence_id": get_next_evidence_id(),
            "study_title": str(article.get("title", ""))[:500],
            "authors_year": f"{article.get('year', '2024')}-01-01",
            "journal": str(article.get("journal", ""))[:200],
            "toxin_domain": mapped_domain,
            "condition_id": condition_id or "",
            "evidence_type": sanitize_evidence_type(extracted.get("evidence_type", "")),
            "sample_size": str(extracted.get("sample_size", ""))[:50],
            "markers_covered": biomarkers_str[:1000],
            "key_findings": str(extracted.get("key_findings", ""))[:2000],
            "effect_size": str(extracted.get("effect_size", ""))[:200],
            "clinical_relevance": str(extracted.get("clinical_relevance", ""))[:1000],
            "limitations": str(extracted.get("limitations", ""))[:1000],
            "evidence_strength_score": format_stars(stars),
            "source_url": str(article.get("url", ""))
        }
    }
    
    # Auto-linking
    try:
        if condition_id:
            health_condition_rec_id = find_health_condition_link(condition_id)
            if health_condition_rec_id:
                record["fields"]["health_condition_link"] = [health_condition_rec_id]
                print(f"   🔗 Linked to Health_Conditions: {condition_id}")
        
        if condition_id:
            symptom_cluster_rec_ids = find_symptom_cluster_links(condition_id)
            if symptom_cluster_rec_ids:
                record["fields"]["symptom_clusters_link"] = symptom_cluster_rec_ids
                print(f"   🔗 Linked to {len(symptom_cluster_rec_ids)} Symptom_Clusters")
    
    except Exception as e:
        print(f"   ⚠️ Linking error (continuing anyway): {e}")
    
    record["fields"] = {k: v for k, v in record["fields"].items() if v and (not isinstance(v, str) or v.strip())}
    
    try:
        response = requests.post(url, headers=headers, json=record, timeout=30)
        response.raise_for_status()
        stats["added_to_airtable"] += 1
        print(f"   ✅ Added: {format_stars(stars)} | {mapped_domain}")
        return True
    except requests.exceptions.RequestException as e:
        print(f"   ❌ Airtable error: {e}")
        if hasattr(e, 'response') and e.response is not None:
            print(f"   Response: {e.response.text[:500]}")
        stats["errors"] += 1
        return False


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def load_config():
    """Load configuration from config.yaml"""
    try:
        with open("config.yaml", "r") as f:
            return yaml.safe_load(f)
    except FileNotFoundError:
        print("⚠️ config.yaml not found, using defaults")
        return {
            "search": {
                "keywords": [
                    "longevity biomarkers blood",
                    "biological age blood markers",
                ],
                "date_after": "2024-06-01",
                "max_results": 25
            },
            "scoring": {
                "min_score_to_save": 3
            }
        }


def main():
    """Main execution flow"""
    print("=" * 60)
    print("🧬 LONGEVITY EVIDENCE SCOUT v1.4")
    print("   Title Weighting + Negative Keyword Exclusions")
    print("=" * 60)
    print(f"⏰ Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    if not ANTHROPIC_KEY:
        print("❌ ANTHROPIC_KEY not set!")
        sys.exit(1)
    if not AIRTABLE_API_KEY:
        print("❌ AIRTABLE_API_KEY not set!")
        sys.exit(1)
    
    print(f"📊 Airtable Base: {AIRTABLE_BASE_ID}")
    print(f"📋 Table: {AIRTABLE_TABLE_NAME}")
    print()
    
    config = load_config()
    keywords = config.get("search", {}).get("keywords", [])
    date_after = config.get("search", {}).get("date_after", "2024-06-01")
    max_results = config.get("search", {}).get("max_results", 25)
    min_score = config.get("scoring", {}).get("min_score_to_save", 3)
    
    print(f"📅 Date filter: After {date_after}")
    print(f"🔍 Keyword groups: {len(keywords)}")
    print(f"⭐ Min score threshold: {min_score}")
    print()
    
    # Pre-load domain keywords
    load_domain_keywords(config)
    
    # Pre-load caches for auto-linking
    print("📥 Loading related tables for auto-linking...")
    load_health_conditions()
    load_symptom_clusters()
    print()
    
    existing_titles = get_existing_titles()
    
    for i, keyword in enumerate(keywords, 1):
        print(f"\n{'='*60}")
        print(f"🔎 [{i}/{len(keywords)}] Searching: {keyword[:50]}...")
        print("=" * 60)
        
        pmids = search_pubmed(keyword, max_results, date_after)
        print(f"   Found {len(pmids)} articles")
        
        for pmid in pmids:
            time.sleep(0.4)

            article = fetch_pubmed_abstract(pmid)
            if not article or not article.get("abstract"):
                continue

            title_lower = article["title"].lower().strip()
            if title_lower in existing_titles:
                print(f"   ⏭️ Duplicate: {article['title'][:50]}...")
                stats["duplicates_skipped"] += 1
                continue

            # v1.5: Abstract-level inpatient exclusion — runs BEFORE Claude call
            excluded, matched_phrase = is_inpatient_study(
                article["title"], article["abstract"]
            )
            if excluded:
                print(f"   🏥 Inpatient excluded ({matched_phrase}): {article['title'][:50]}...")
                stats["inpatient_excluded"] += 1
                continue

            # v1.4: Use new domain detection with title weighting
            domain = detect_domain(
                article["title"],
                article["abstract"],
                keyword,
                config
            )

            print(f"   🤖 Analyzing: {article['title'][:50]}...")
            extracted = ask_claude(article, domain)
            if not extracted:
                continue

            # v1.5: population_type gate — skip confirmed inpatient studies
            pop_type = extracted.get("population_type", "not specified").lower().strip()
            if "inpatient" in pop_type:
                print(f"   🏥 Claude flagged inpatient population — skipping")
                stats["population_type_excluded"] += 1
                continue

            stars = calculate_stars(
                extracted.get("evidence_type", ""),
                extracted.get("sample_size", ""),
                article["journal"],
                extracted.get("effect_size", "")
            )

            if stars < min_score:
                print(f"   ⏭️ Below threshold ({format_stars(stars)})")
                stats["below_threshold"] += 1
                continue

            if add_to_airtable(article, extracted, stars, domain):
                existing_titles.add(title_lower)
    
    print("\n" + "=" * 60)
    print("📊 SUMMARY")
    print("=" * 60)
    print(f"   🔍 Articles searched: {stats['total_searched']}")
    print(f"   📄 Abstracts fetched: {stats['abstracts_fetched']}")
    print(f"   ⏭️ Duplicates skipped: {stats['duplicates_skipped']}")
    print(f"   🏥 Inpatient excluded (abstract): {stats['inpatient_excluded']}")
    print(f"   🏥 Inpatient excluded (Claude): {stats['population_type_excluded']}")
    print(f"   📉 Below threshold: {stats['below_threshold']}")
    print(f"   ✅ Added to Airtable: {stats['added_to_airtable']}")
    print(f"   ❌ Errors: {stats['errors']}")
    print(f"   ⏰ Completed: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 60)
    
    sys.exit(0)


if __name__ == "__main__":
    main()
